//! Creates MIR expressions from HIR expressions.

use std::collections::BTreeMap;

use quill_common::{location::Ranged, name::QualifiedName};
use quill_parser::{expr_pat::ConstantValue, identifier::NameP};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::hir::{
    definition::{Definition, DefinitionBody, DefinitionCase},
    expr::{Expression, ExpressionContents},
    pattern::Pattern,
};

use crate::{
    definition::{to_mir_def, DefinitionTranslationContext},
    mir::*,
    pattern_match::perform_match_function,
};

/// Sets up the context for dealing with this expression.
pub(crate) fn initialise_expr(ctx: &mut DefinitionTranslationContext, expr: &Expression) {
    match &expr.contents {
        ExpressionContents::Argument(_) => {}
        ExpressionContents::Local(_) => {}
        ExpressionContents::Symbol { .. } => {}
        ExpressionContents::Apply(left, right) => {
            initialise_expr(ctx, left);
            initialise_expr(ctx, right);
        }
        ExpressionContents::Lambda { .. } => {}
        ExpressionContents::Let { name, expr, .. } => {
            ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty: expr.ty.clone(),
                name: Some(name.name.clone()),
            });
        }
        ExpressionContents::Block { statements, .. } => {
            for stmt in statements {
                initialise_expr(ctx, stmt);
            }
        }
        ExpressionContents::ConstructData { fields, .. } => {
            for (_, expr) in fields {
                initialise_expr(ctx, expr);
            }
        }
        ExpressionContents::ConstantValue { .. } => {}
        ExpressionContents::Borrow { expr, .. } => initialise_expr(ctx, &*expr),
        ExpressionContents::Copy { expr, .. } => initialise_expr(ctx, &*expr),
        ExpressionContents::Impl { .. } => {}
        ExpressionContents::Match { expr, cases, .. } => {
            initialise_expr(ctx, &*expr);
            for (_, expr) in cases {
                initialise_expr(ctx, expr);
            }
        }
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
        ExpressionContents::Argument(arg) => vec![arg.clone()],
        ExpressionContents::Local(local) => vec![local.clone()],
        ExpressionContents::Symbol { .. } => Vec::new(),
        ExpressionContents::Apply(l, r) => {
            let mut result = list_used_locals(l);
            result.extend(list_used_locals(r));
            result
        }
        ExpressionContents::Lambda { params, expr, .. } => {
            // Remove the lambda parameter names from the list.
            let mut result = list_used_locals(&*expr);
            result.retain(|name| params.iter().all(|(param_name, _)| param_name != name));
            result
        }
        ExpressionContents::Let { expr, .. } => list_used_locals(&*expr),
        ExpressionContents::Block { statements, .. } => {
            let mut result = statements
                .iter()
                .map(list_used_locals)
                .flatten()
                .collect::<Vec<_>>();
            let let_locals = statements
                .iter()
                .filter_map(|stmt| {
                    if let ExpressionContents::Let { name, .. } = &stmt.contents {
                        Some(name.clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();
            result.retain(|name| !let_locals.contains(name));
            result
        }
        ExpressionContents::ConstructData { fields, .. } => fields
            .iter()
            .map(|(_, field_expr)| list_used_locals(field_expr))
            .flatten()
            .collect::<Vec<_>>(),
        ExpressionContents::ConstantValue { .. } => Vec::new(),
        ExpressionContents::Borrow { expr, .. } => list_used_locals(&*expr),
        ExpressionContents::Copy { expr, .. } => list_used_locals(&*expr),
        ExpressionContents::Impl { .. } => {
            /* TODO
            implementations
            .values()
            .flatten()
            .map(|f| list_used_locals(&*f.replacement))
            .flatten()
            .collect()
            */
            todo!()
            // Vec::new()
        }
        ExpressionContents::Match {
            match_token,
            expr,
            cases,
        } => todo!(),
    }
}

/// If we're in a lambda, we might need to use some captured local variables.
/// However, they aren't considered local variables any more; they're really arguments
/// passed to the expanded lambda. So we need to convert these locals into arguments.
fn convert_locals_to_args(mut expr: Expression, locals: Vec<NameP>) -> Expression {
    if let ExpressionContents::Local(l) = &expr.contents {
        for local in &locals {
            if local.name == l.name {
                expr.contents = ExpressionContents::Argument(local.clone());
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
        ExpressionContents::Argument(arg) => generate_expr_argument(ctx, terminator, arg),
        ExpressionContents::Local(local) => generate_expr_local(ctx, terminator, local),
        ExpressionContents::Symbol {
            name,
            range,
            type_variables,
        } => generate_expr_symbol(ctx, range, ty, terminator, name, type_variables),
        ExpressionContents::Apply(left, right) => {
            generate_expr_apply(ctx, range, ty, terminator, left, right)
        }
        ExpressionContents::Lambda {
            lambda_token,
            params,
            expr,
        } => generate_expr_lambda(expr, params, ctx, lambda_token, range, terminator, ty),
        ExpressionContents::Let {
            name,
            expr: right_expr,
            ..
        } => generate_expr_let(ctx, range, name, terminator, right_expr),
        ExpressionContents::Block { statements, .. } => {
            generate_expr_block(statements, ctx, range, terminator)
        }
        ExpressionContents::ConstructData {
            fields, variant, ..
        } => generate_expr_construct(fields, ctx, range, ty, terminator, variant),
        ExpressionContents::ConstantValue { value, range } => {
            generate_expr_constant(ctx, range, ty, value, terminator)
        }
        ExpressionContents::Borrow { borrow_token, expr } => {
            generate_expr_borrow(ctx, range, expr, terminator, borrow_token)
        }
        ExpressionContents::Copy { copy_token, expr } => {
            generate_expr_copy(ctx, range, expr, terminator, copy_token)
        }
        ExpressionContents::Impl {
            implementations, ..
        } => generate_expr_impl(ty, implementations, ctx, range, terminator),
        ExpressionContents::Match { expr, cases, .. } => {
            generate_expr_match(ctx, range, terminator, ty, expr, cases)
        }
    }
}

fn generate_expr_argument(
    ctx: &mut DefinitionTranslationContext,
    terminator: Terminator,
    arg: NameP,
) -> ExprGeneratedM {
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

fn generate_expr_local(
    ctx: &mut DefinitionTranslationContext,
    terminator: Terminator,
    local: NameP,
) -> ExprGeneratedM {
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

fn generate_expr_symbol(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    terminator: Terminator,
    name: QualifiedName,
    type_variables: Vec<Type>,
) -> ExprGeneratedM {
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

fn generate_expr_apply(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    terminator: Terminator,
    left: Box<Expression>,
    right: Box<Expression>,
) -> ExprGeneratedM {
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
                argument: Box::new(Rvalue::Move(Place::new(right.variable))),
                function: Box::new(Rvalue::Move(Place::new(left.variable))),
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

fn generate_expr_lambda(
    expr: Box<Expression>,
    params: Vec<(NameP, Type)>,
    ctx: &mut DefinitionTranslationContext,
    lambda_token: quill_common::location::Range,
    range: quill_common::location::Range,
    terminator: Terminator,
    ty: Type,
) -> ExprGeneratedM {
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
                argument: Box::new(Rvalue::Move(Place {
                    local: ctx.get_name_of_local(&local.name),
                    projection: Vec::new(),
                })),
                function: Box::new(Rvalue::Move(Place {
                    local: LocalVariableName::Local(variable),
                    projection: Vec::new(),
                })),
                target: LocalVariableName::Local(next_variable),
                return_type: ty,
                argument_type: ctx.local_variable_names[&ctx.get_name_of_local(&local.name)]
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

fn generate_expr_let(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    name: NameP,
    terminator: Terminator,
    right_expr: Box<Expression>,
) -> ExprGeneratedM {
    let ret = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: Type::Primitive(PrimitiveType::Unit),
        name: None,
    });
    let variable = ctx.get_name_of_local(&name.name);
    let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });
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
            source: Rvalue::Move(Place::new(rvalue.variable)),
        },
    });
    statements.push(Statement {
        range,
        kind: StatementKind::Assign {
            target: LocalVariableName::Local(ret),
            source: Rvalue::Constant(ConstantValue::Unit),
        },
    });
    rvalue.locals_to_drop.push(variable);
    ExprGeneratedM {
        block: rvalue.block,
        variable: LocalVariableName::Local(ret),
        locals_to_drop: rvalue.locals_to_drop,
        // The result of the let statement is the unit value, which is a temporary
        // even though the actual value in the let statement is not temporary.
    }
}

fn generate_expr_block(
    mut statements: Vec<Expression>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
) -> ExprGeneratedM {
    let locals_to_drop = statements
        .iter()
        .filter_map(|expr| {
            if let ExpressionContents::Let { name, .. } = &expr.contents {
                Some(name.name.clone())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
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
                source: Rvalue::Constant(ConstantValue::Unit),
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

fn generate_expr_construct(
    fields: Vec<(NameP, Expression)>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    terminator: Terminator,
    variant: Option<String>,
) -> ExprGeneratedM {
    let (names, expressions): (Vec<_>, Vec<_>) = fields.into_iter().unzip();
    let variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: ty.clone(),
        name: None,
    });
    let construct_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: vec![],
        terminator,
    });
    let chain = generate_chain_with_terminator(
        ctx,
        expressions,
        Terminator {
            range,
            kind: TerminatorKind::Goto(construct_variable),
        },
    );
    let construct = Statement {
        range,
        kind: StatementKind::ConstructData {
            ty,
            variant,
            fields: chain
                .variables
                .into_iter()
                .zip(names)
                .map(|(name, field_name)| (field_name.name, Rvalue::Move(Place::new(name))))
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
    ExprGeneratedM {
        block: chain.block,
        variable: LocalVariableName::Local(variable),
        locals_to_drop: chain.locals_to_drop,
    }
}

fn generate_expr_constant(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    value: ConstantValue,
    terminator: Terminator,
) -> ExprGeneratedM {
    let variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty,
        name: None,
    });
    let assign = Statement {
        range,
        kind: StatementKind::Assign {
            target: LocalVariableName::Local(variable),
            source: Rvalue::Constant(value),
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

fn generate_expr_borrow(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    expr: Box<Expression>,
    terminator: Terminator,
    borrow_token: quill_common::location::Range,
) -> ExprGeneratedM {
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

fn generate_expr_copy(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    expr: Box<Expression>,
    terminator: Terminator,
    copy_token: quill_common::location::Range,
) -> ExprGeneratedM {
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
                source: Rvalue::Copy(inner.variable),
            },
        });
    ExprGeneratedM {
        block: inner.block,
        variable: LocalVariableName::Local(variable),
        locals_to_drop: inner.locals_to_drop,
    }
}

fn generate_expr_impl(
    ty: Type,
    implementations: BTreeMap<String, Definition>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
) -> ExprGeneratedM {
    let (aspect, type_variables) = if let Type::Impl { name, parameters } = ty.clone() {
        (name, parameters)
    } else {
        unreachable!()
    };
    let def_types = implementations
        .values()
        .map(|def| {
            let mut symbol_type = def.return_type.clone();
            for arg in def.arg_types.iter().rev() {
                symbol_type = Type::Function(Box::new(arg.clone()), Box::new(symbol_type));
            }
            symbol_type
        })
        .collect::<Vec<_>>();
    let mut def_numbers = Vec::new();
    for (name, def) in implementations {
        def_numbers.push((name, *ctx.lambda_number));
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
    }
    let mut statements = Vec::new();
    let mut definitions = BTreeMap::new();
    let variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty,
        name: None,
    });
    for ((def_name, def_number), def_type) in def_numbers.into_iter().zip(def_types) {
        let def_variable = ctx.new_local_variable(LocalVariableInfo {
            range,
            ty: def_type,
            name: None,
        });
        definitions.insert(def_name, LocalVariableName::Local(def_variable));

        statements.push(Statement {
            range,
            kind: StatementKind::InstanceSymbol {
                name: QualifiedName {
                    source_file: ctx.source_file.clone(),
                    name: format!("{}/lambda/{}", ctx.def_name, def_number),
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
                target: LocalVariableName::Local(def_variable),
            },
        });
    }
    statements.push(Statement {
        range,
        kind: StatementKind::ConstructImpl {
            aspect,
            type_variables,
            definitions,
            target: LocalVariableName::Local(variable),
        },
    });
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

fn generate_expr_match(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
    ty: Type,
    expr: Box<Expression>,
    cases: Vec<(Pattern, Expression)>,
) -> ExprGeneratedM {
    // Generate the block for the result of this expression.
    // The result of the match expression is assigned to `result`.
    let result = ctx.new_local_variable(LocalVariableInfo {
        range: expr.range(),
        ty,
        name: None,
    });
    // Create a dummy basic block which all of the other blocks will redirect to after finishing.
    let final_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });

    // Generate each case.
    let (patterns, replacements): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    let replacements = replacements
        .into_iter()
        .map(|replacement| {
            // Generate a basic block to move the value of the generated expression into `result`.
            let terminator_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator {
                    range: expr.range(),
                    kind: TerminatorKind::Goto(final_block),
                },
            });
            let expr_result = generate_expr(
                ctx,
                replacement,
                Terminator {
                    range: expr.range(),
                    kind: TerminatorKind::Goto(terminator_block),
                },
            );
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&terminator_block)
                .unwrap()
                .statements
                .push(Statement {
                    range: expr.range(),
                    kind: StatementKind::Assign {
                        target: LocalVariableName::Local(result),
                        source: Rvalue::Move(Place::new(expr_result.variable)),
                    },
                });
            expr_result.block
        })
        .collect::<Vec<_>>();

    // Now that each case has been generated, perform the actual pattern match operation.
    // We treat this as a single-argument function for purposes of pattern matching.
    let cases = patterns
        .into_iter()
        .map(|pat| vec![pat])
        .zip(replacements)
        .collect();
    let block = perform_match_function(ctx.project_index, ctx, range, vec![expr.ty.clone()], cases);
    ExprGeneratedM {
        block,
        variable: LocalVariableName::Local(result),
        locals_to_drop: Vec::new(),
    }
}
