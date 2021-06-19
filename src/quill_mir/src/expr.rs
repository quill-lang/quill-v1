//! Creates MIR expressions from HIR expressions.

use quill_common::{location::Ranged, name::QualifiedName};
use quill_parser::{expr_pat::ConstantValue, identifier::NameP};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::type_check::{
    Definition, DefinitionBody, DefinitionCase, Expression, ExpressionContentsGeneric, Pattern,
};

use crate::{
    definition::{to_mir_def, DefinitionTranslationContext},
    mir::*,
};

/// Sets up the context for dealing with this expression.
pub(crate) fn initialise_expr(ctx: &mut DefinitionTranslationContext, expr: &Expression) {
    match &expr.contents {
        ExpressionContentsGeneric::Argument(_) => {}
        ExpressionContentsGeneric::Local(_) => {}
        ExpressionContentsGeneric::Symbol { .. } => {}
        ExpressionContentsGeneric::Apply(left, right) => {
            initialise_expr(ctx, left);
            initialise_expr(ctx, right);
        }
        ExpressionContentsGeneric::Lambda { .. } => {}
        ExpressionContentsGeneric::Let { name, expr, .. } => {
            ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty: expr.ty.clone(),
                name: Some(name.name.clone()),
            });
        }
        ExpressionContentsGeneric::Block { statements, .. } => {
            for stmt in statements {
                initialise_expr(ctx, stmt);
            }
        }
        ExpressionContentsGeneric::ConstructData { fields, .. } => {
            for (_, expr) in fields {
                initialise_expr(ctx, expr);
            }
        }
        ExpressionContentsGeneric::ConstantValue { .. } => {}
        ExpressionContentsGeneric::Borrow { expr, .. } => initialise_expr(ctx, &*expr),
        ExpressionContentsGeneric::Copy { expr, .. } => initialise_expr(ctx, &*expr),
    }
}

pub(crate) struct ExprGeneratedM {
    /// The basic block that will, once called, compute the value of this expression, and store it in the given local variable.
    pub block: BasicBlockId,
    /// The target that will have the expression's result stored into it.
    pub variable: LocalVariableName,
    /// Some expressions require temporary variables to be kept alive until the end of a statement.
    /// By adding values to this list, the given local variables will be dropped after the surrounding statement (or expression) ends.
    /// In particular, the drop occurs at the next semicolon, or if there is not one, the end of the definition as a whole.
    pub locals_to_drop: Vec<LocalVariableName>,
}

/// Creates a list of all local or argument variables used inside this expression.
fn list_used_locals(expr: &Expression) -> Vec<NameP> {
    match &expr.contents {
        ExpressionContentsGeneric::Argument(arg) => vec![arg.clone()],
        ExpressionContentsGeneric::Local(local) => vec![local.clone()],
        ExpressionContentsGeneric::Symbol { .. } => Vec::new(),
        ExpressionContentsGeneric::Apply(l, r) => {
            let mut result = list_used_locals(l);
            result.extend(list_used_locals(r));
            result
        }
        ExpressionContentsGeneric::Lambda { params, expr, .. } => {
            // Remove the lambda parameter names from the list.
            let mut result = list_used_locals(&*expr);
            result.retain(|name| params.iter().all(|(param_name, _)| param_name != name));
            result
        }
        ExpressionContentsGeneric::Let { expr, .. } => list_used_locals(&*expr),
        ExpressionContentsGeneric::Block { statements, .. } => {
            let mut result = statements
                .iter()
                .map(list_used_locals)
                .flatten()
                .collect::<Vec<_>>();
            let let_locals = statements
                .iter()
                .filter_map(|stmt| {
                    if let ExpressionContentsGeneric::Let { name, .. } = &stmt.contents {
                        Some(name.clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            result.retain(|name| !let_locals.contains(name));
            result
        }
        ExpressionContentsGeneric::ConstructData { fields, .. } => fields
            .iter()
            .map(|(_, field_expr)| list_used_locals(field_expr))
            .flatten()
            .collect::<Vec<_>>(),
        ExpressionContentsGeneric::ConstantValue { .. } => Vec::new(),
        ExpressionContentsGeneric::Borrow { expr, .. } => list_used_locals(&*expr),
        ExpressionContentsGeneric::Copy { expr, .. } => list_used_locals(&*expr),
    }
}

/// If we're in a lambda, we might need to use some captured local variables.
/// However, they aren't considered local variables any more; they're really arguments
/// passed to the expanded lambda. So we need to convert these locals into arguments.
fn convert_locals_to_args(mut expr: Expression, locals: Vec<NameP>) -> Expression {
    if let ExpressionContentsGeneric::Local(l) = &expr.contents {
        for local in &locals {
            if local.name == l.name {
                expr.contents = ExpressionContentsGeneric::Argument(local.clone());
                break;
            }
        }
    }
    expr
}

struct ChainGeneratedM {
    /// The basic block that will, once called, compute the values in this chain, and store it in the given local variables.
    block: BasicBlockId,
    /// The targets that will have the chain's results stored into them.
    variables: Vec<LocalVariableName>,
    /// Some expressions require temporary variables to be kept alive until the end of a statement.
    /// By adding values to this list, the given local variables will be dropped after the surrounding statement (or expression) ends.
    /// In particular, the drop occurs at the next semicolon, or if there is not one, the end of the definition as a whole.
    locals_to_drop: Vec<LocalVariableName>,
}

/// Generates a chain of expressions, with the given terminator.
/// Returns the basic block that can be invoked in order to invoke the chain, along with the variables
/// produced by each expression.
fn generate_chain_with_terminator(
    ctx: &mut DefinitionTranslationContext,
    exprs: Vec<Expression>,
    mut terminator: Terminator,
) -> ChainGeneratedM {
    let range = terminator.range;

    let mut first_block = None;
    let mut locals = Vec::new();
    let mut locals_to_drop = Vec::new();

    for expr in exprs.into_iter().rev() {
        let gen = generate_expr(ctx, expr, terminator);
        locals.insert(0, gen.variable);
        terminator = Terminator {
            range,
            kind: TerminatorKind::Goto(gen.block),
        };
        first_block = Some(gen.block);
        locals_to_drop.extend(gen.locals_to_drop);
    }

    let first_block = first_block.unwrap_or_else(|| {
        ctx.control_flow_graph.new_basic_block(BasicBlock {
            statements: Vec::new(),
            terminator,
        })
    });

    ChainGeneratedM {
        block: first_block,
        variables: locals,
        locals_to_drop,
    }
}

/// Generates a basic block that computes the value of this expression, and stores the result in the given local.
/// The block generated will have the given terminator.
pub(crate) fn generate_expr(
    ctx: &mut DefinitionTranslationContext,
    expr: Expression,
    terminator: Terminator,
) -> ExprGeneratedM {
    let range = expr.range();
    let ty = expr.ty;
    match expr.contents {
        ExpressionContentsGeneric::Argument(arg) => {
            // Create an empty basic block.
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let variable = ctx.get_name_of_local(&arg.name);
            ExprGeneratedM {
                block,
                variable,
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Local(local) => {
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let variable = ctx.get_name_of_local(&local.name);
            ExprGeneratedM {
                block,
                variable,
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Symbol {
            name,
            range,
            type_variables,
        } => {
            // Instantiate the given symbol.
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![Statement {
                    range,
                    kind: StatementKind::InstanceSymbol {
                        name,
                        type_variables,
                        target: LocalVariableName::Local(variable),
                    },
                }],
                terminator,
            });
            ExprGeneratedM {
                block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Apply(left, right) => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });

            let (argument_type, return_type) = if let Type::Function(l, r) = left.ty.clone() {
                (*l, *r)
            } else {
                unreachable!()
            };

            let right = generate_expr(
                ctx,
                *right,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );
            let left = generate_expr(
                ctx,
                *left,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(right.block),
                },
            );

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements
                .push(Statement {
                    range,
                    kind: StatementKind::Apply {
                        argument: Box::new(Rvalue::Use(Operand::Move(Place::new(right.variable)))),
                        function: Box::new(Rvalue::Use(Operand::Move(Place::new(left.variable)))),
                        target: LocalVariableName::Local(variable),
                        return_type,
                        argument_type,
                    },
                });

            ExprGeneratedM {
                block: left.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: left
                    .locals_to_drop
                    .into_iter()
                    .chain(right.locals_to_drop)
                    .collect(),
            }
        }
        ExpressionContentsGeneric::Lambda {
            lambda_token,
            params,
            expr,
        } => {
            // Create a new definition for this lambda.
            // Move all used variables inside the lambda definition.
            let mut used_variables = list_used_locals(&*expr);
            used_variables.retain(|name| params.iter().all(|(param_name, _)| param_name != name));
            used_variables.sort_by(|a, b| a.name.cmp(&b.name));
            used_variables.dedup();
            let arg_types = used_variables
                .iter()
                .map(|name| {
                    ctx.local_variable_names[&ctx.get_name_of_local(&name.name)]
                        .ty
                        .clone()
                })
                .chain(params.iter().map(|(_, ty)| ty.clone()))
                .collect::<Vec<_>>();
            let def = Definition {
                range: lambda_token,
                type_variables: ctx.type_variables.clone(),
                arg_types,
                return_type: expr.ty.clone(),
                body: DefinitionBody::PatternMatch(vec![DefinitionCase {
                    range,
                    arg_patterns: used_variables
                        .iter()
                        .chain(params.iter().map(|(n, _)| n))
                        .map(|n| Pattern::Named(n.clone()))
                        .collect(),
                    replacement: convert_locals_to_args(
                        *expr,
                        used_variables
                            .iter()
                            .cloned()
                            .chain(params.iter().map(|(n, _)| n.clone()))
                            .collect(),
                    ),
                }]),
            };
            let lambda_number = *ctx.lambda_number;
            *ctx.lambda_number += 1;
            let (inner, inner_inner) = to_mir_def(
                ctx.project_index,
                def,
                ctx.source_file,
                ctx.def_name,
                ctx.lambda_number,
            );
            ctx.additional_definitions.push(inner);
            ctx.additional_definitions.extend(inner_inner);

            // Now that we've created the lambda as a definition, we need to instance this lambda into scope.
            // In particular, we need to call this new definition a few times to supply the list of used locals.
            let mut curry_types = vec![ty];
            for var in &used_variables {
                curry_types.push(Type::Function(
                    Box::new(
                        ctx.local_variable_names[&ctx.get_name_of_local(&var.name)]
                            .ty
                            .clone(),
                    ),
                    Box::new(curry_types.last().unwrap().clone()),
                ));
            }
            let mut statements = Vec::new();
            let mut variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: curry_types.pop().unwrap(),
                name: None,
            });
            statements.push(Statement {
                range,
                kind: StatementKind::InstanceSymbol {
                    name: QualifiedName {
                        source_file: ctx.source_file.clone(),
                        name: format!("{}/lambda/{}", ctx.def_name, lambda_number),
                        range,
                    },
                    type_variables: ctx
                        .type_variables
                        .iter()
                        .map(|param| Type::Variable {
                            variable: param.name.clone(),
                            parameters: Vec::new(),
                        })
                        .collect(),
                    target: LocalVariableName::Local(variable),
                },
            });
            for (local, ty) in used_variables
                .into_iter()
                .zip(curry_types.into_iter().rev())
            {
                // Apply the variable to this local.
                let next_variable = ctx.new_local_variable(LocalVariableInfo {
                    range,
                    ty: ty.clone(),
                    name: None,
                });
                statements.push(Statement {
                    range,
                    kind: StatementKind::Apply {
                        argument: Box::new(Rvalue::Use(Operand::Move(Place {
                            local: ctx.get_name_of_local(&local.name),
                            projection: Vec::new(),
                        }))),
                        function: Box::new(Rvalue::Use(Operand::Move(Place {
                            local: LocalVariableName::Local(variable),
                            projection: Vec::new(),
                        }))),
                        target: LocalVariableName::Local(next_variable),
                        return_type: ty,
                        argument_type: ctx.local_variable_names
                            [&ctx.get_name_of_local(&local.name)]
                            .ty
                            .clone(),
                    },
                });
                variable = next_variable;
            }

            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements,
                terminator,
            });
            ExprGeneratedM {
                block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Let {
            name,
            expr: right_expr,
            ..
        } => {
            // Let expressions return the unit value.
            let ret = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: Type::Primitive(PrimitiveType::Unit),
                name: None,
            });

            // Let expressions are handled in two phases. First, (before calling this function)
            // we initialise the context with a blank variable of the right name and type, so that
            // other expressions can access it. Then, we assign a value to the variable in this function now.
            let variable = ctx.get_name_of_local(&name.name);
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });

            // Create the RHS of the let expression, and assign it to the LHS.
            let mut rvalue = generate_expr(
                ctx,
                *right_expr,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );

            let statements = &mut ctx
                .control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements;

            statements.push(Statement {
                range,
                kind: StatementKind::Assign {
                    target: variable,
                    source: Rvalue::Use(Operand::Move(Place::new(rvalue.variable))),
                },
            });
            statements.push(Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(ret),
                    source: Rvalue::Use(Operand::Constant(ConstantValue::Unit)),
                },
            });

            rvalue.locals_to_drop.push(variable);

            ExprGeneratedM {
                block: rvalue.block,
                variable: LocalVariableName::Local(ret),
                locals_to_drop: rvalue.locals_to_drop,
            }
        }
        ExpressionContentsGeneric::Block { mut statements, .. } => {
            // Make a list of all the local variables we'll need to drop at the end of this scope.
            let locals_to_drop = statements
                .iter()
                .filter_map(|expr| {
                    if let ExpressionContentsGeneric::Let { name, .. } = &expr.contents {
                        Some(name.name.clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            // Make a basic block that drops these variables, in reverse order.
            let drop_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: locals_to_drop
                    .iter()
                    .rev()
                    .map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive {
                            variable: ctx.get_name_of_local(local),
                        },
                    })
                    .collect(),
                terminator,
            });
            let drop_terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(drop_block),
            };

            if let Some(final_expression) = statements.pop() {
                let final_expr = generate_expr(ctx, final_expression, drop_terminator);

                let mut chain = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(final_expr.block),
                    },
                );
                chain.locals_to_drop.extend(chain.variables);
                chain.locals_to_drop.extend(final_expr.locals_to_drop);
                ctx.control_flow_graph
                    .basic_blocks
                    .get_mut(&drop_block)
                    .unwrap()
                    .statements
                    .extend(chain.locals_to_drop.into_iter().map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive { variable: local },
                    }));

                ExprGeneratedM {
                    block: chain.block,
                    variable: final_expr.variable,
                    locals_to_drop: Vec::new(),
                }
            } else {
                // We need to make a new unit variable since there was no final expression.
                // This is the variable that is returned by the block.
                let variable = ctx.new_local_variable(LocalVariableInfo {
                    range,
                    ty: Type::Primitive(PrimitiveType::Unit),
                    name: None,
                });

                // Initialise the variable with an empty value.
                let assign = Statement {
                    range,
                    kind: StatementKind::Assign {
                        target: LocalVariableName::Local(variable),
                        source: Rvalue::Use(Operand::Constant(ConstantValue::Unit)),
                    },
                };

                let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: vec![assign],
                    terminator: drop_terminator,
                });

                let mut chain = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(initialise_variable),
                    },
                );
                chain.locals_to_drop.extend(chain.variables);
                ctx.control_flow_graph
                    .basic_blocks
                    .get_mut(&drop_block)
                    .unwrap()
                    .statements
                    .extend(chain.locals_to_drop.into_iter().map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive { variable: local },
                    }));

                ExprGeneratedM {
                    block: chain.block,
                    variable: LocalVariableName::Local(variable),
                    locals_to_drop: Vec::new(),
                }
            }
        }
        ExpressionContentsGeneric::ConstructData {
            fields, variant, ..
        } => {
            // Break each field into its name and its expression.
            let (names, expressions): (Vec<_>, Vec<_>) = fields.into_iter().unzip();

            // Now, construct the data.
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: ty.clone(),
                name: None,
            });

            // Create a block to initialise the variable with its new value.
            let construct_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![],
                terminator,
            });

            // Chain the construction of the fields.
            let chain = generate_chain_with_terminator(
                ctx,
                expressions,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(construct_variable),
                },
            );

            // Now, after we've constructed the fields, make the new variable with them.
            let construct = Statement {
                range,
                kind: StatementKind::ConstructData {
                    ty,
                    variant,
                    fields: chain
                        .variables
                        .into_iter()
                        .zip(names)
                        .map(|(name, field_name)| {
                            (
                                field_name.name,
                                Rvalue::Use(Operand::Move(Place::new(name))),
                            )
                        })
                        .collect(),
                    target: LocalVariableName::Local(variable),
                },
            };
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&construct_variable)
                .unwrap()
                .statements
                .push(construct);

            // Finally, chain the construction of the new variable with its fields.

            ExprGeneratedM {
                block: chain.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: chain.locals_to_drop,
            }
        }
        ExpressionContentsGeneric::ConstantValue { value, range } => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

            // Initialise the variable with an empty value.
            let assign = Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(variable),
                    source: Rvalue::Use(Operand::Constant(value)),
                },
            };

            let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![assign],
                terminator,
            });

            ExprGeneratedM {
                block: initialise_variable,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Borrow { borrow_token, expr } => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: Type::Borrow {
                    ty: Box::new(expr.ty.clone()),
                    borrow: None,
                },
                name: None,
            });
            let terminator_range = terminator.range;
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let mut inner = generate_expr(
                ctx,
                *expr,
                Terminator {
                    range: terminator_range,
                    kind: TerminatorKind::Goto(block),
                },
            );
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements
                .push(Statement {
                    range: borrow_token,
                    kind: StatementKind::Assign {
                        target: LocalVariableName::Local(variable),
                        source: Rvalue::Borrow(inner.variable),
                    },
                });
            inner
                .locals_to_drop
                .push(LocalVariableName::Local(variable));
            ExprGeneratedM {
                block: inner.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: inner.locals_to_drop,
            }
        }
        ExpressionContentsGeneric::Copy { copy_token, expr } => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: if let Type::Borrow { ty, .. } = expr.ty.clone() {
                    *ty
                } else {
                    unreachable!()
                },
                name: None,
            });
            let terminator_range = terminator.range;
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let inner = generate_expr(
                ctx,
                *expr,
                Terminator {
                    range: terminator_range,
                    kind: TerminatorKind::Goto(block),
                },
            );
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements
                .push(Statement {
                    range: copy_token,
                    kind: StatementKind::Assign {
                        target: LocalVariableName::Local(variable),
                        source: Rvalue::Use(Operand::Copy(Place {
                            local: inner.variable,
                            projection: Vec::new(),
                        })),
                    },
                });
            ExprGeneratedM {
                block: inner.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: inner.locals_to_drop,
            }
        }
    }
}
