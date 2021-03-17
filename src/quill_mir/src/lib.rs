//! This module contains the m range: (), kind: ()id-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

use std::collections::HashMap;

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Location, Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_parser::NameP;
use quill_type::Type;
use quill_type_deduce::type_check::{Definition, ImmediateValue, Pattern, SourceFileHIR};

/// A parsed, type checked, and borrow checked source file.
#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, DefinitionM>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ArgumentIndex(pub u64);
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LocalVariableId(pub u64);
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct BasicBlockId(pub u64);

/// A local variable is a value which can be operated on by functions and expressions.
/// Other objects, such as symbols in global scope, must be instanced as local variables
/// before being operated on. This allows the borrow checker and the code translator
/// to better understand the control flow and data flow.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub enum LocalVariableName {
    /// An argument starts as being 'owned'.
    /// Parts of arguments, such as pattern-matched components, are explicitly
    /// retrieved from an argument by a MIR expression in the function body.
    Argument(ArgumentIndex),
    /// Local variables, such as intermediate values, are given a unique ID to distinguish them.
    Local(LocalVariableId),
    /// The return value can be written to (but not read from) using this enum value.
    ReturnValue,
}

/// A definition for a symbol, i.e. a function or constant.
/// The function's type is `arg_types -> return_type`.
/// For example, if we defined a function
/// ```notrust
/// def foo: int -> int -> int {
///     foo a b = a
/// }
/// ```
/// then `arg_types` would be `[int, int]` and `return_type` would be `int`. If instead we defined it as
/// ```notrust
/// def foo: int -> int -> int {
///     foo a = \b -> a
/// }
/// ```
/// then `arg_types` would be `[int]` and `return_type` would be `int -> int`.
///
/// Further, in this struct, different pattern match cases in a function are unified into one control flow graph,
/// where the pattern matching is carried out explicitly. Local variables from each case are unified into one list.
#[derive(Debug)]
pub struct DefinitionM {
    range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<String>,
    /// How many parameters must be supplied to this function? Their types are kept in the local variable names map.
    pub arity: u64,
    /// Contains argument types and return types.
    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
    /// Which basic block should be entered to invoke the function?
    pub entry_point: BasicBlockId,
}

impl Ranged for DefinitionM {
    fn range(&self) -> Range {
        self.range
    }
}

/// Information about a local variable, either explicitly or implicitly defined.
#[derive(Debug)]
pub struct LocalVariableInfo {
    /// Where was the local variable defined?
    /// If this is just an expression, then this is the range of the expression.
    pub range: Range,
    /// What is the exact type of this variable?
    pub ty: Type,
    /// If this variable had a name, what was it?
    pub name: Option<String>,
}

#[derive(Debug)]
pub struct ControlFlowGraph {
    next_block_id: BasicBlockId,
    /// Every basic block has a unique index, which is its index inside this basic blocks map.
    /// When jumping between basic blocks, we must provide the index of the target block.
    pub basic_blocks: HashMap<BasicBlockId, BasicBlock>,
}

impl ControlFlowGraph {
    /// Inserts a new basic block into the control flow graph, and returns its new unique ID.
    pub fn new_basic_block(&mut self, basic_block: BasicBlock) -> BasicBlockId {
        let id = self.next_block_id;
        self.next_block_id.0 += 1;
        self.basic_blocks.insert(id, basic_block);
        id
    }
}

/// A basic block is a block of code that can be executed, and may manipulate values.
/// Control flow is entirely linear inside a basic block.
/// After this basic block, we may branch to one of several places.
#[derive(Debug)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub struct Statement {
    pub range: Range,
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign { target: Place, source: Rvalue },
}

/// A place in memory that we can read from and write to.
#[derive(Debug, Clone)]
pub struct Place {
    /// The local variable that the place originates from.
    local: LocalVariableName,
    /// A list of lenses that allow us to index inside this local variable into deeper and deeper nested places.
    projection: Vec<PlaceSegment>,
}

impl Place {
    pub fn new(local: LocalVariableName) -> Self {
        Place {
            local,
            projection: Vec::new(),
        }
    }

    pub fn then(mut self, segment: PlaceSegment) -> Self {
        self.projection.push(segment);
        self
    }
}

#[derive(Debug, Clone)]
pub enum PlaceSegment {
    Field(String),
}

/// Represents the use of a value that we can feed into an expression or function.
/// We can only read from (not write to) an rvalue.
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// Either a copy or a move, depending on the type.
    Use(Operand),
}

/// A value that we can read from.
#[derive(Debug, Clone)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(ImmediateValue),
}

#[derive(Debug)]
pub struct Terminator {
    pub range: Range,
    pub kind: TerminatorKind,
}

#[derive(Debug)]
pub enum TerminatorKind {
    /// Jump to another basic block unconditionally.
    Goto(BasicBlockId),
    /// Works out which variant of a enum type a given local variable is.
    SwitchDiscriminator {
        cases: HashMap<QualifiedName, BasicBlockId>,
    },
    /// Used in intermediate steps, when we do not know the terminator of a block.
    /// This should never be translated into LLVM IR, the compiler should instead panic.
    Invalid,
}

/// Converts all expressions into control flow graphs.
pub fn to_mir(
    source_file: &SourceFileIdentifier,
    file: SourceFileHIR,
) -> DiagnosticResult<SourceFileMIR> {
    let definitions = file
        .definitions
        .into_iter()
        .map(|(def_name, def)| to_mir_def(def).map(|def| (def_name, def)))
        .collect::<DiagnosticResult<Vec<_>>>();

    definitions.map(|definitions| SourceFileMIR {
        definitions: definitions.into_iter().collect(),
    })
}

/// While we're translating a definition into MIR, this structure is passed around
/// all the expressions so that we can keep a definition-wide log of all the variables
/// we're using.
struct DefinitionTranslationContext {
    next_local_variable_id: LocalVariableId,

    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
}

impl DefinitionTranslationContext {
    /// Creates a new local variable with the given information,
    /// that is by default not initialised.
    pub fn new_local_variable(&mut self, info: LocalVariableInfo) -> LocalVariableName {
        let id = self.next_local_variable_id;
        self.next_local_variable_id.0 += 1;
        self.local_variable_names
            .insert(LocalVariableName::Local(id), info);
        LocalVariableName::Local(id)
    }
}

fn to_mir_def(def: Definition) -> DiagnosticResult<DefinitionM> {
    let mut ctx = DefinitionTranslationContext {
        next_local_variable_id: LocalVariableId(0),
        local_variable_names: HashMap::new(),
        control_flow_graph: ControlFlowGraph {
            next_block_id: BasicBlockId(0),
            basic_blocks: HashMap::new(),
        },
    };

    let range = def.range();
    let type_variables = def.type_variables.clone();
    let arg_types = def.arg_types.clone();

    ctx.local_variable_names.insert(
        LocalVariableName::ReturnValue,
        LocalVariableInfo {
            range: def.range(),
            ty: def.return_type.clone(),
            name: Some("return value".to_string()),
        },
    );

    // This function will create the rest of the control flow graph
    // for sub-expressions.
    let entry_point = create_cfg(&mut ctx, def);

    DiagnosticResult::ok(DefinitionM {
        range,
        type_variables,
        arity: arg_types.len() as u64,
        local_variable_names: ctx.local_variable_names,
        control_flow_graph: ctx.control_flow_graph,
        entry_point,
    })
}

/// Creates a control flow graph for a function definition.
/// Returns the basic block representing the function's entry point.
fn create_cfg(ctx: &mut DefinitionTranslationContext, def: Definition) -> BasicBlockId {
    // Begin by creating the CFG for each case in the definition.
    let range = def.range();
    for case in def.cases {
        // Create a local variable for each bound variable in the pattern.
        let unwrap_patterns_blocks = case
            .arg_patterns
            .iter()
            .zip(&def.arg_types)
            .enumerate()
            .filter_map(|(i, (arg_pattern, arg_type))| {
                bind_pattern_variables(
                    ctx,
                    Place::new(LocalVariableName::Argument(ArgumentIndex(i as u64))),
                    arg_pattern,
                    arg_type.clone(),
                )
            })
            .collect::<Vec<_>>();

        let unwrap_patterns_block = chain(ctx, unwrap_patterns_blocks, range);

        if true {
            return unwrap_patterns_block;
        }
    }

    panic!()
}

/// Creates a basic block (or tree of basic blocks) that
/// performs the given pattern matching operation.
/// The value is matched against each case, and basic blocks are created that branch to
/// these 'case' blocks when the pattern is matched. The return value is a basic block
/// which will perform this match operation, then jump to the case blocks.
fn perform_match(
    ctx: &mut DefinitionTranslationContext,
    value: LocalVariableName,
    cases: HashMap<Pattern, BasicBlockId>,
) -> BasicBlockId {
    unimplemented!()
}

/// Chains a series of basic blocks together, assuming that they do not have terminators.
/// Returns a single basic block.
fn chain(
    ctx: &mut DefinitionTranslationContext,
    blocks: Vec<BasicBlockId>,
    range: Range,
) -> BasicBlockId {
    let blocks = blocks
        .into_iter()
        .map(|block_id| {
            ctx.control_flow_graph
                .basic_blocks
                .remove(&block_id)
                .unwrap()
        })
        .collect::<Vec<_>>();

    ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: blocks
            .into_iter()
            .map(|block| {
                assert!(matches!(block.terminator.kind, TerminatorKind::Invalid));
                block.statements
            })
            .flatten()
            .collect(),
        terminator: Terminator {
            range,
            kind: TerminatorKind::Invalid,
        },
    })
}

/// Creates a local variable for each bound variable in a pattern, assuming that the given value
/// has the given pattern, and the given type.
/// Returns a basic block that initialises these variables, and that terminates with the given terminator.
/// If no variables need to be initialised, returns None.
fn bind_pattern_variables(
    ctx: &mut DefinitionTranslationContext,
    value: Place,
    pat: &Pattern,
    ty: Type,
) -> Option<BasicBlockId> {
    match pat {
        Pattern::Named(name) => {
            let var = ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty,
                name: Some(name.name.clone()),
            });

            // Initialise this local variable with the supplied value.
            let stmt = Statement {
                range: name.range,
                kind: StatementKind::Assign {
                    target: Place::new(var),
                    source: Rvalue::Use(Operand::Move(value)),
                },
            };

            Some(ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![stmt],
                terminator: Terminator {
                    range: name.range,
                    kind: TerminatorKind::Invalid,
                },
            }))
        }
        Pattern::TypeConstructor { type_ctor, fields } => {
            // Bind each field individually, then chain all the blocks together.
            let blocks = fields
                .iter()
                .filter_map(|(field_name, ty, pat)| {
                    bind_pattern_variables(
                        ctx,
                        value
                            .clone()
                            .then(PlaceSegment::Field(field_name.name.clone())),
                        pat,
                        ty.clone(),
                    )
                })
                .collect::<Vec<_>>();
            if blocks.is_empty() {
                None
            } else {
                Some(chain(ctx, blocks, type_ctor.range))
            }
        }
        Pattern::Function { .. } => {
            unreachable!("functions are forbidden in arg patterns")
        }
        Pattern::Unknown(_) => None,
    }
}
