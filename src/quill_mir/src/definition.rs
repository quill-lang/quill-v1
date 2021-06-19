//! Converts HIR function definitions into MIR.

use std::collections::{BTreeMap, HashMap};

use quill_common::location::{Range, Ranged, SourceFileIdentifier};
use quill_index::{ProjectIndex, TypeParameter};
use quill_type::Type;
use quill_type_deduce::hir::definition::{Definition, DefinitionBody, DefinitionCase};

use crate::{
    expr::{generate_expr, initialise_expr},
    mir::*,
    pattern_match::{bind_pattern_variables, perform_match_function},
};

/// While we're translating a definition into MIR, this structure is passed around
/// all the expressions so that we can keep a definition-wide log of all the variables
/// we're using.
pub(crate) struct DefinitionTranslationContext<'a> {
    next_local_variable_id: LocalVariableId,
    /// Retrieves the unique name of a named local variable.
    local_name_map: HashMap<String, LocalVariableName>,

    pub local_variable_names: BTreeMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
    pub type_variables: Vec<TypeParameter>,
    pub project_index: &'a ProjectIndex,
    /// Sometimes we need to create additional function definitions in MIR
    /// from a single function in HIR. Most commonly, this occurs when creating
    /// lambdas. If they are stored in this list, they will be output with the rest of the MIR.
    pub additional_definitions: Vec<DefinitionM>,
    /// Tracks how many lambdas we've made in this entire function, including inner functions.
    /// When the root function is done, the `additional_definitions` list will have indices
    /// that match up with the `lambda_number` at the time of the lambda's creation.
    pub lambda_number: &'a mut usize,
    pub source_file: &'a SourceFileIdentifier,
    pub def_name: &'a str,
}

impl DefinitionTranslationContext<'_> {
    /// Creates a new local variable with the given information,
    /// that is by default not initialised.
    /// If `info` provides a name, the `local_name_map` is updated.
    pub fn new_local_variable(&mut self, info: LocalVariableInfo) -> LocalVariableId {
        let id = self.next_local_variable_id;
        self.next_local_variable_id.0 += 1;
        if let Some(name) = info.name.clone() {
            self.local_name_map
                .insert(name, LocalVariableName::Local(id));
        }
        self.local_variable_names
            .insert(LocalVariableName::Local(id), info);
        id
    }

    pub fn get_name_of_local(&self, local: &str) -> LocalVariableName {
        // println!("Local: {}, Map: {:#?}", local, self.local_name_map);
        self.local_name_map[local]
    }
}

/// Returns a definition, and a list of inner additional definitions.
/// Additional definitions may be created if we need to construct additional functions
/// that are not visible in the global scope, e.g. lambdas.
///
/// `lambda_number` tracks the amount of lambdas and other inner functions we've created, allowing us to
/// assign a unique number to each one.
pub(crate) fn to_mir_def(
    project_index: &ProjectIndex,
    def: Definition,
    source_file: &SourceFileIdentifier,
    def_name: &str,
    lambda_number: &mut usize,
) -> (DefinitionM, Vec<DefinitionM>) {
    let range = def.range();
    let type_variables = def.type_variables.clone();
    let arity = def.arg_types.len() as u64;
    let return_type = def.return_type.clone();

    let mut local_variable_names = BTreeMap::new();

    for (i, ty) in def.arg_types.iter().enumerate() {
        local_variable_names.insert(
            LocalVariableName::Argument(ArgumentIndex(i as u64)),
            LocalVariableInfo {
                range,
                ty: ty.clone(),
                name: None,
            },
        );
    }

    match def.body {
        DefinitionBody::PatternMatch(cases) => {
            let mut ctx = DefinitionTranslationContext {
                next_local_variable_id: LocalVariableId(0),
                local_variable_names,
                local_name_map: HashMap::new(),
                control_flow_graph: ControlFlowGraph::new(),
                type_variables: type_variables.clone(),
                project_index,
                additional_definitions: Vec::new(),
                lambda_number,
                source_file,
                def_name,
            };

            // This function will create the rest of the control flow graph
            // for sub-expressions.
            ctx.control_flow_graph.entry_point =
                create_cfg(project_index, &mut ctx, cases, def.arg_types, range);
            ctx.control_flow_graph.reorder();

            let def = DefinitionM {
                range,
                type_variables,
                arity,
                local_variable_names: ctx.local_variable_names,
                return_type,
                body: DefinitionBodyM::PatternMatch(ctx.control_flow_graph),
            };

            (def, ctx.additional_definitions)
        }

        DefinitionBody::CompilerIntrinsic => {
            let def = DefinitionM {
                range,
                type_variables,
                arity,
                local_variable_names,
                return_type,
                body: DefinitionBodyM::CompilerIntrinsic,
            };

            (def, Vec::new())
        }
    }
}

/// Creates a control flow graph for a function definition.
/// Returns the basic block representing the function's entry point.
fn create_cfg(
    project_index: &ProjectIndex,
    ctx: &mut DefinitionTranslationContext,
    cases: Vec<DefinitionCase>,
    arg_types: Vec<Type>,
    range: Range,
) -> BasicBlockId {
    // Begin by creating the CFG for each case in the definition.
    let cases = cases
        .into_iter()
        .map(|case| {
            // Create a local variable for each bound variable in the pattern.
            let all_bound_pattern_variables = case
                .arg_patterns
                .iter()
                .zip(&arg_types)
                .enumerate()
                .map(|(i, (arg_pattern, arg_type))| {
                    bind_pattern_variables(
                        ctx,
                        project_index,
                        Place::new(LocalVariableName::Argument(ArgumentIndex(i as u64))),
                        arg_pattern,
                        arg_type.clone(),
                    )
                })
                .map(|result| (result.statements, result.bound_variables));

            let mut unwrap_patterns_blocks = Vec::new();
            let mut bound_variables = Vec::new();
            for (more_statements, more_bound_variables) in all_bound_pattern_variables {
                unwrap_patterns_blocks.extend(more_statements);
                bound_variables.extend(more_bound_variables);
            }

            let unwrap_patterns_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: unwrap_patterns_blocks,
                terminator: Terminator {
                    range,
                    kind: TerminatorKind::Invalid,
                },
            });

            // Now let's build the end of the function, specifically the code to return a value.
            let return_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator {
                    range,
                    kind: TerminatorKind::Invalid,
                },
            });

            // Now, we can generate basic blocks for the rest of the function.
            initialise_expr(ctx, &case.replacement);
            let func = generate_expr(
                ctx,
                case.replacement,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(return_block),
                },
            );

            // Before we return `func.variable` from our function, we first need to drop any locals that have not yet
            // been dropped. We will simply accomplish this by moving the return value into a "protected" variable,
            // and then drop every other variable that could possibly be alive at this point.
            let protected_return_value = ctx.new_local_variable(LocalVariableInfo {
                range: ctx.local_variable_names[&func.variable].range,
                ty: ctx.local_variable_names[&func.variable].ty.clone(),
                name: Some("return value".to_string()),
            });
            // Move the return value into this protected slot.
            let return_block = ctx
                .control_flow_graph
                .basic_blocks
                .get_mut(&return_block)
                .unwrap();
            return_block.statements.push(Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(protected_return_value),
                    source: Rvalue::Use(Operand::Move(Place {
                        local: func.variable,
                        projection: Vec::new(),
                    })),
                },
            });

            // Further, we need to drop the function's arguments (if they're still alive) in this return block.
            // Variables bound using patterns may not have been dropped at this point.
            // We drop these before dropping arguments.
            for temp in func.locals_to_drop {
                return_block.statements.push(Statement {
                    range,
                    kind: StatementKind::DropIfAlive { variable: temp },
                })
            }
            for temp in bound_variables {
                return_block.statements.push(Statement {
                    range,
                    kind: StatementKind::DropIfAlive { variable: temp },
                })
            }
            for i in 0..arg_types.len() {
                return_block.statements.push(Statement {
                    range,
                    kind: StatementKind::DropIfAlive {
                        variable: LocalVariableName::Argument(ArgumentIndex(i as u64)),
                    },
                })
            }
            // Now, replace the terminator with a custom terminator that returns the real protected return value from the function.
            return_block.terminator = Terminator {
                range,
                kind: TerminatorKind::Return {
                    value: LocalVariableName::Local(protected_return_value),
                },
            };

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&unwrap_patterns_block)
                .unwrap()
                .terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(func.block),
            };

            (case.arg_patterns, unwrap_patterns_block)
        })
        .collect::<Vec<_>>();

    // Then perform the pattern matching operation on each parameter to the function, in reverse order.
    perform_match_function(project_index, ctx, range, arg_types, cases)
}
