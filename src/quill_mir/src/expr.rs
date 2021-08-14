//! Creates MIR expressions from HIR expressions.

use std::collections::{BTreeMap, BTreeSet};

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_parser::{expr_pat::ConstantValue, identifier::NameP};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::{
    hir::{
        definition::{Definition, DefinitionBody, DefinitionCase},
        expr::{Expression, ExpressionContents},
        pattern::Pattern,
    },
    replace_type_variables,
};

use crate::{
    definition::{to_mir_def, DefinitionTranslationContext},
    impls::find_and_apply_default_impl,
    mir::*,
    pattern_match::{bind_pattern_variables, perform_match_function},
};

/// Sets up the context for dealing with this expression.
/// This sets up slots for all local variables that are defined in this expression.
pub(crate) fn initialise_expr(ctx: &mut DefinitionTranslationContext, expr: &Expression) {
    match &expr.contents {
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
            for (_pat, expr) in cases {
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
}

/// Creates a list of all local or argument variables used inside this expression.
fn list_used_locals(expr: &Expression) -> Vec<NameP> {
    match &expr.contents {
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
        ExpressionContents::Match { expr, cases, .. } => {
            let mut result = cases
                .iter()
                .map(|(_, expr)| list_used_locals(expr))
                .flatten()
                .chain(list_used_locals(&*expr))
                .collect::<Vec<_>>();
            let arg_names = cases
                .iter()
                .map(|(pat, _)| bound_variable_names(pat))
                .flatten()
                .collect::<BTreeSet<_>>();
            result.retain(|name| !arg_names.contains(name));
            result
        }
    }
}

struct ChainGeneratedM {
    /// The basic block that will, once called, compute the values in this chain, and store it in the given local variables.
    block: BasicBlockId,
    /// The targets that will have the chain's results stored into them.
    variables: Vec<LocalVariableName>,
}

/// Generates a chain of expressions, with the given terminator.
/// Returns the basic block that can be invoked in order to invoke the chain, along with the variables
/// produced by each expression.
fn generate_chain_with_terminator(
    ctx: &mut DefinitionTranslationContext,
    exprs: Vec<Expression>,
    mut terminator: Terminator,
) -> DiagnosticResult<ChainGeneratedM> {
    let mut messages = Vec::new();
    let range = terminator.range;

    let mut first_block = None;
    let mut locals = Vec::new();

    for expr in exprs.into_iter().rev() {
        let (gen, more_messages) = generate_expr(ctx, expr, terminator).destructure();
        if let Some(gen) = gen {
            locals.insert(0, gen.variable);
            terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(gen.block),
            };
            first_block = Some(gen.block);
        } else {
            terminator = Terminator {
                range,
                kind: TerminatorKind::Invalid,
            };
        }
        messages.extend(more_messages);
    }

    let first_block = first_block.unwrap_or_else(|| {
        ctx.control_flow_graph.new_basic_block(BasicBlock {
            statements: Vec::new(),
            terminator,
        })
    });

    DiagnosticResult::ok_with_many(
        ChainGeneratedM {
            block: first_block,
            variables: locals,
        },
        messages,
    )
}

/// Generates a basic block that computes the value of this expression, and stores the result in the given local.
/// The block generated will have the given terminator.
pub(crate) fn generate_expr(
    ctx: &mut DefinitionTranslationContext,
    expr: Expression,
    terminator: Terminator,
) -> DiagnosticResult<ExprGeneratedM> {
    let range = expr.range();
    // `ty` is the expected value of the expression *after* type coercion.
    // TODO: because of this, we should *not* feed `ty` into the `generate_expr_*` functions.
    let ty = expr.ty;

    // Create a dummy block. The expression terminator will point into this block.
    let coerce_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });
    let new_terminator = Terminator {
        range,
        kind: TerminatorKind::Goto(coerce_block),
    };

    let result = match expr.contents {
        ExpressionContents::Local(local) => generate_expr_local(ctx, new_terminator, local),
        ExpressionContents::Symbol {
            name,
            range,
            type_variables,
        } => generate_expr_symbol(ctx, range, new_terminator, name, type_variables),
        ExpressionContents::Apply(left, right) => {
            generate_expr_apply(ctx, range, ty.clone(), new_terminator, left, right)
        }
        ExpressionContents::Lambda {
            lambda_token,
            params,
            expr,
        } => generate_expr_lambda(
            expr,
            params,
            ctx,
            lambda_token,
            range,
            new_terminator,
            ty.clone(),
        ),
        ExpressionContents::Let {
            name,
            expr: right_expr,
            ..
        } => generate_expr_let(ctx, range, name, new_terminator, right_expr),
        ExpressionContents::Block { statements, .. } => {
            generate_expr_block(statements, ctx, range, new_terminator)
        }
        ExpressionContents::ConstructData {
            fields, variant, ..
        } => generate_expr_construct(fields, ctx, range, ty.clone(), new_terminator, variant),
        ExpressionContents::ConstantValue { value, range } => {
            generate_expr_constant(ctx, range, ty.clone(), value, new_terminator)
        }
        ExpressionContents::Borrow { borrow_token, expr } => {
            generate_expr_borrow(ctx, range, expr, new_terminator, borrow_token)
        }
        ExpressionContents::Copy { copy_token, expr } => {
            generate_expr_copy(ctx, range, expr, new_terminator, copy_token)
        }
        ExpressionContents::Impl {
            implementations, ..
        } => generate_expr_impl(ty.clone(), implementations, ctx, range, new_terminator),
        ExpressionContents::Match { expr, cases, .. } => {
            generate_expr_match(ctx, range, new_terminator, ty.clone(), expr, cases)
        }
    };

    result.bind(|result| coerce(ctx, range, result, ty, coerce_block))
}

/// Coerce the given expression into the given type.
/// If coercion could not be done (for example, if an impl does not exist for a type),
/// then an error message will be emitted.
///
/// `coerce_block` is a block that we can use to insert coercion instructions.
/// It is guaranteed to be just after the `expr` creation code.
fn coerce(
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    mut expr: ExprGeneratedM,
    mut ty: Type,
    coerce_block: BasicBlockId,
) -> DiagnosticResult<ExprGeneratedM> {
    let mut original_ty = ctx.locals[&expr.variable].ty.clone().anonymise_borrows();
    ty = ty.anonymise_borrows();

    if original_ty == ty {
        return expr.into();
    }

    // Work out all the requirements we need in order to coerce original_ty into ty.
    let mut messages = Vec::new();
    while let Type::Function(l, r) = original_ty {
        if let Type::Impl { name, parameters } = *l {
            // Check if there exists a default impl.
            let (val, more_messages) =
                find_and_apply_default_impl(ctx, range, &name, &parameters, &expr).destructure();
            messages.extend(more_messages);
            if let Some(val) = val {
                expr.variable = val.variable;
                ctx.control_flow_graph
                    .basic_blocks
                    .get_mut(&coerce_block)
                    .unwrap()
                    .statements
                    .extend(val.statements);
            }
            original_ty = *r;
        } else {
            break;
        }

        if original_ty == ty {
            break;
        }
    }
    DiagnosticResult::ok_with_many(expr, messages)
}

fn generate_expr_local(
    ctx: &mut DefinitionTranslationContext,
    terminator: Terminator,
    local: NameP,
) -> DiagnosticResult<ExprGeneratedM> {
    let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });
    let variable = ctx.get_name_of_local(&local.name);
    ExprGeneratedM { block, variable }.into()
}

fn generate_expr_symbol(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
    name: QualifiedName,
    type_variables: Vec<Type>,
) -> DiagnosticResult<ExprGeneratedM> {
    let def = ctx.project_index.definition(&name);
    let ty = replace_type_variables(
        def.symbol_type.clone(),
        &def.type_variables,
        &type_variables,
    );
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
    }
    .into()
}

fn generate_expr_apply(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    terminator: Terminator,
    left: Box<Expression>,
    right: Box<Expression>,
) -> DiagnosticResult<ExprGeneratedM> {
    let variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty,
        name: None,
    });
    let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });
    let right = generate_expr(
        ctx,
        *right,
        Terminator {
            range,
            kind: TerminatorKind::Goto(block),
        },
    );
    right.bind(|right| {
        let left = generate_expr(
            ctx,
            *left,
            Terminator {
                range,
                kind: TerminatorKind::Goto(right.block),
            },
        );
        left.map(|left| {
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
                    },
                });
            ExprGeneratedM {
                block: left.block,
                variable: LocalVariableName::Local(variable),
            }
        })
    })
}

fn generate_expr_lambda(
    expr: Box<Expression>,
    params: Vec<(NameP, Type)>,
    ctx: &mut DefinitionTranslationContext,
    lambda_token: quill_common::location::Range,
    range: quill_common::location::Range,
    terminator: Terminator,
    ty: Type,
) -> DiagnosticResult<ExprGeneratedM> {
    let mut used_variables = list_used_locals(&*expr);
    used_variables.retain(|name| params.iter().all(|(param_name, _)| param_name != name));
    used_variables.sort_by(|a, b| a.name.cmp(&b.name));
    used_variables.dedup();
    let arg_types = used_variables
        .iter()
        .map(|name| ctx.locals[&ctx.get_name_of_local(&name.name)].ty.clone())
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
            replacement: *expr,
        }]),
    };
    let lambda_number = *ctx.lambda_number;
    *ctx.lambda_number += 1;
    to_mir_def(
        ctx.project_index,
        def,
        ctx.source_file,
        ctx.def_name,
        ctx.lambda_number,
    )
    .map(|(inner, inner_inner)| {
        ctx.additional_definitions.push(inner);
        ctx.additional_definitions.extend(inner_inner);
        let mut curry_types = vec![ty];
        for var in used_variables.iter().rev() {
            curry_types.push(Type::Function(
                Box::new(ctx.locals[&ctx.get_name_of_local(&var.name)].ty.clone()),
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
        }
    })
}

fn generate_expr_let(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    name: NameP,
    terminator: Terminator,
    right_expr: Box<Expression>,
) -> DiagnosticResult<ExprGeneratedM> {
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
    let rvalue = generate_expr(
        ctx,
        *right_expr,
        Terminator {
            range,
            kind: TerminatorKind::Goto(block),
        },
    );
    rvalue.map(|rvalue| {
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
        ExprGeneratedM {
            block: rvalue.block,
            variable: LocalVariableName::Local(ret),
        }
    })
}

fn generate_expr_block(
    mut statements: Vec<Expression>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
) -> DiagnosticResult<ExprGeneratedM> {
    let drop_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });
    let drop_terminator = Terminator {
        range,
        kind: TerminatorKind::Goto(drop_block),
    };
    if let Some(final_expression) = statements.pop() {
        let final_expr = generate_expr(ctx, final_expression, drop_terminator);
        final_expr.bind(|final_expr| {
            let chain = generate_chain_with_terminator(
                ctx,
                statements,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(final_expr.block),
                },
            );

            chain.map(|chain| ExprGeneratedM {
                block: chain.block,
                variable: final_expr.variable,
            })
        })
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

        let chain = generate_chain_with_terminator(
            ctx,
            statements,
            Terminator {
                range,
                kind: TerminatorKind::Goto(initialise_variable),
            },
        );

        chain.map(|chain| ExprGeneratedM {
            block: chain.block,
            variable: LocalVariableName::Local(variable),
        })
    }
}

fn generate_expr_construct(
    fields: Vec<(NameP, Expression)>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    terminator: Terminator,
    variant: Option<String>,
) -> DiagnosticResult<ExprGeneratedM> {
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
    chain.map(|chain| {
        let construct = Statement {
            range,
            kind: if let Type::Named { name, parameters } = ty {
                StatementKind::ConstructData {
                    name,
                    type_variables: parameters,
                    variant,
                    fields: chain
                        .variables
                        .into_iter()
                        .zip(names)
                        .map(|(name, field_name)| (field_name.name, Rvalue::Move(Place::new(name))))
                        .collect(),
                    target: LocalVariableName::Local(variable),
                }
            } else {
                unreachable!()
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
        }
    })
}

fn generate_expr_constant(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    ty: Type,
    value: ConstantValue,
    terminator: Terminator,
) -> DiagnosticResult<ExprGeneratedM> {
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
    }
    .into()
}

fn generate_expr_borrow(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    expr: Box<Expression>,
    terminator: Terminator,
    borrow_token: quill_common::location::Range,
) -> DiagnosticResult<ExprGeneratedM> {
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
    let inner = generate_expr(
        ctx,
        *expr,
        Terminator {
            range: terminator_range,
            kind: TerminatorKind::Goto(block),
        },
    );
    inner.map(|inner| {
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
        ExprGeneratedM {
            block: inner.block,
            variable: LocalVariableName::Local(variable),
        }
    })
}

fn generate_expr_copy(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    expr: Box<Expression>,
    terminator: Terminator,
    copy_token: quill_common::location::Range,
) -> DiagnosticResult<ExprGeneratedM> {
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
    inner.map(|inner| {
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
        }
    })
}

fn generate_expr_impl(
    ty: Type,
    implementations: BTreeMap<String, Definition>,
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
) -> DiagnosticResult<ExprGeneratedM> {
    let (aspect, type_variables) = if let Type::Impl { name, parameters } = ty.clone() {
        (name, parameters)
    } else {
        unreachable!()
    };
    let mut def_numbers = Vec::new();

    implementations
        .into_iter()
        .map(|(name, mut def)| {
            let body = if let DefinitionBody::PatternMatch(body) = def.body {
                body
            } else {
                panic!("cannot have intrinsic body in impl")
            };
            let mut used_variables = body
                .iter()
                .map(|case| list_used_locals(&case.replacement))
                .flatten()
                .collect::<Vec<_>>();
            let arg_names = body
                .iter()
                .map(|case| case.arg_patterns.iter().map(bound_variable_names))
                .flatten()
                .flatten()
                .collect::<BTreeSet<_>>();
            used_variables.retain(|name| !arg_names.contains(name));
            used_variables.sort_by(|a, b| a.name.cmp(&b.name));
            used_variables.dedup();
            let arg_types = used_variables
                .iter()
                .map(|name| ctx.locals[&ctx.get_name_of_local(&name.name)].ty.clone());

            // Reconstruct the def body, adding the new args to each case.
            def.body = DefinitionBody::PatternMatch(
                body.into_iter()
                    .map(|mut case| {
                        for used_variable in used_variables.iter().rev() {
                            case.arg_patterns
                                .insert(0, Pattern::Named(used_variable.clone()));
                        }
                        case
                    })
                    .collect(),
            );
            for used_variable_ty in arg_types.into_iter().rev() {
                def.arg_types.insert(0, used_variable_ty);
            }
            def.type_variables = ctx
                .type_variables
                .iter()
                .cloned()
                .chain(def.type_variables)
                .collect();

            let lambda_number = *ctx.lambda_number;
            def_numbers.push((name.clone(), lambda_number));
            *ctx.lambda_number += 1;
            to_mir_def(
                ctx.project_index,
                def,
                ctx.source_file,
                ctx.def_name,
                ctx.lambda_number,
            )
            .map(|(inner, inner_inner)| {
                let mut original_def_ty = inner.return_type.clone();
                for i in ((used_variables.len() as u64)..inner.arity).rev() {
                    original_def_ty = Type::Function(
                        Box::new(
                            inner.local_variable_names
                                [&LocalVariableName::Argument(ArgumentIndex(i))]
                                .ty
                                .clone(),
                        ),
                        Box::new(original_def_ty),
                    );
                }

                ctx.additional_definitions.push(inner);
                ctx.additional_definitions.extend(inner_inner);

                let mut curry_types = vec![original_def_ty];
                for var in used_variables.iter().rev() {
                    curry_types.push(Type::Function(
                        Box::new(ctx.locals[&ctx.get_name_of_local(&var.name)].ty.clone()),
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
                        },
                    });
                    variable = next_variable;
                }

                ((name, LocalVariableName::Local(variable)), statements)
            })
        })
        .collect::<DiagnosticResult<Vec<_>>>()
        .map(|statements| {
            let (definitions, statements): (BTreeMap<_, _>, Vec<_>) =
                statements.into_iter().unzip();
            let mut statements = statements.into_iter().flatten().collect::<Vec<_>>();
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

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
            }
        })
}

fn bound_variable_names(pat: &Pattern) -> Vec<NameP> {
    match pat {
        Pattern::Named(name) => vec![name.clone()],
        Pattern::Constant { .. } => Vec::new(),
        Pattern::TypeConstructor { fields, .. } => fields
            .iter()
            .map(|(_, _, pat)| bound_variable_names(pat))
            .flatten()
            .collect(),
        Pattern::Impl { fields, .. } => fields
            .iter()
            .map(|(_, _, pat)| bound_variable_names(pat))
            .flatten()
            .collect(),
        Pattern::Function { args, .. } => args.iter().map(bound_variable_names).flatten().collect(),
        Pattern::Borrow { borrowed, .. } => bound_variable_names(&*borrowed),
        Pattern::Unknown(_) => Vec::new(),
    }
}

fn generate_expr_match(
    ctx: &mut DefinitionTranslationContext,
    range: quill_common::location::Range,
    terminator: Terminator,
    ty: Type,
    expr: Box<Expression>,
    cases: Vec<(Pattern, Expression)>,
) -> DiagnosticResult<ExprGeneratedM> {
    // Generate the source expression we are pattern matching on.
    // First, create a dummy block that will jump to the pattern match operation.
    let dummy = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator: Terminator {
            range: expr.range(),
            kind: TerminatorKind::Invalid,
        },
    });
    let source_range = expr.range();
    let source_ty = expr.ty.clone();
    let source = generate_expr(
        ctx,
        *expr,
        Terminator {
            range: source_range,
            kind: TerminatorKind::Goto(dummy),
        },
    );

    // Generate the block for the result of this expression.
    // The result of the match expression is assigned to `result`.
    let result = ctx.new_local_variable(LocalVariableInfo {
        range: source_range,
        ty,
        name: None,
    });
    // Create a dummy basic block which all of the other blocks will redirect to after finishing.
    // This final block will drop the contents of the source expression.
    let final_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: Vec::new(),
        terminator,
    });

    // Generate each case.
    let (patterns, replacements): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    source.bind(|source| {
        let replacements = replacements
            .into_iter()
            .zip(patterns.iter())
            .map(|(replacement, pattern)| {
                // Generate a dummy basic block to act as a signal to move the value of the generated expression
                // into `result` conditionally using a Phi node.
                let terminator_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator {
                        range: source_range,
                        kind: TerminatorKind::Goto(final_block),
                    },
                });

                // Bind all of the variables we created in the pattern.
                let bound_variables = bind_pattern_variables(
                    ctx,
                    Place::new(source.variable),
                    pattern,
                    source_ty.clone(),
                    None,
                );

                // Compute the replacement expression.
                let expr_result = generate_expr(
                    ctx,
                    replacement,
                    Terminator {
                        range: source_range,
                        kind: TerminatorKind::Goto(terminator_block),
                    },
                );

                expr_result.map(|expr_result| {
                    // Create a block which will bind all the locals then jump to the replacement block.
                    let bind_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                        statements: bound_variables.statements,
                        terminator: Terminator {
                            range: source_range,
                            kind: TerminatorKind::Goto(expr_result.block),
                        },
                    });

                    // Like in a function pattern match, we need to move the result into a special
                    // "protected" slot, then drop all the living bound variables, before returning
                    // from the match.
                    let protected_slot = ctx.new_local_variable(LocalVariableInfo {
                        range: source_range,
                        ty: ctx.locals[&expr_result.variable].ty.clone(),
                        name: None,
                    });
                    let terminator_statements = &mut ctx
                        .control_flow_graph
                        .basic_blocks
                        .get_mut(&terminator_block)
                        .unwrap()
                        .statements;
                    terminator_statements.push(Statement {
                        range: source_range,
                        kind: StatementKind::Assign {
                            target: LocalVariableName::Local(protected_slot),
                            source: Rvalue::Move(Place::new(expr_result.variable)),
                        },
                    });

                    // Return: (
                    //     the block to call in order to execute the expression,
                    //     the terminator block that we jump from in order to reach the final block,
                    //     the expression containing the result of this case
                    // )
                    (
                        bind_block,
                        terminator_block,
                        LocalVariableName::Local(protected_slot),
                    )
                })
            })
            .collect::<DiagnosticResult<Vec<_>>>();

        replacements.map(|replacements| {
            // Now that each case has been generated, perform the actual pattern match operation.
            // We treat this as a single-argument function for purposes of pattern matching.
            let (cases, phi_cases) = patterns
                .into_iter()
                .map(|pat| vec![pat])
                .zip(replacements)
                .map(
                    |(pat, (replacement_block, replacement_final_block, replacement_variable))| {
                        (
                            (pat, replacement_block),
                            (replacement_final_block, replacement_variable),
                        )
                    },
                )
                .unzip();
            let block =
                perform_match_function(ctx, range, vec![source_ty], &[source.variable], cases);

            // Update the dummy to point to the pattern match operation.
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&dummy)
                .unwrap()
                .terminator
                .kind = TerminatorKind::Goto(block);

            // Update the final block to:
            // - assign the result variable based on which pattern match block we came from, and
            // - drop the source expression after we've pattern-matched it.
            let final_statements = &mut ctx
                .control_flow_graph
                .basic_blocks
                .get_mut(&final_block)
                .unwrap()
                .statements;
            final_statements.push(Statement {
                range: source_range,
                kind: StatementKind::AssignPhi {
                    target: LocalVariableName::Local(result),
                    phi_cases,
                },
            });

            ExprGeneratedM {
                block: source.block,
                variable: LocalVariableName::Local(result),
            }
        })
    })
}
