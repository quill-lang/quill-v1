use std::{
    collections::{btree_map::Entry, BTreeMap},
    ops::Deref,
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    definition::DefinitionTranslationContext,
    expr::ExprGeneratedM,
    mir::{
        BasicBlockId, LocalVariableInfo, LocalVariableName, Place, Rvalue, Statement, StatementKind,
    },
};

/// A definition that can be invoked to yield a default impl for an aspect.
struct DefaultImpl {
    def_name: QualifiedName,
    type_params: Vec<Type>,
    params: Vec<DefaultImpl>,
}

/// Given an expression (a function taking an impl), and an impl type (the parameter),
/// find a relevant default impl and apply it to the expression.
/// We insert instructions at the end of `coerce_block`.
pub(crate) fn find_and_apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    name: &QualifiedName,
    parameters: Vec<Type>,
    expr: &ExprGeneratedM,
    coerce_block: BasicBlockId,
) -> DiagnosticResult<ExprGeneratedM> {
    find_default_impl(ctx.project_index, ctx.source_file, range, name, parameters)
        .map(|default_impl| apply_default_impl(ctx, coerce_block, range, expr, default_impl))
}

fn apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    coerce_block: BasicBlockId,
    range: Range,
    expr: &ExprGeneratedM,
    default_impl: DefaultImpl,
) -> ExprGeneratedM {
    let def = ctx.project_index.definition(&default_impl.def_name);

    let argument_type = replace_type_variables(
        def.symbol_type.clone(),
        &def.type_variables,
        &default_impl.type_params,
    );
    let return_type = if let Type::Function(_, r) = &ctx.locals[&expr.variable].ty {
        r.deref().clone()
    } else {
        unreachable!()
    };

    let impl_variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: argument_type.clone(),
        name: None,
    });

    let result_variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: return_type.clone(),
        name: None,
    });

    let statements = &mut ctx
        .control_flow_graph
        .basic_blocks
        .get_mut(&coerce_block)
        .unwrap()
        .statements;

    // Instance the impl.
    statements.push(Statement {
        range,
        kind: StatementKind::InstanceSymbol {
            name: default_impl.def_name,
            type_variables: default_impl.type_params,
            target: LocalVariableName::Local(impl_variable),
        },
    });

    // Apply the arguments.
    if !default_impl.params.is_empty() {
        todo!();
    }

    // Apply the impl to the expr.
    statements.push(Statement {
        range,
        kind: StatementKind::Apply {
            argument: Box::new(Rvalue::Move(Place::new(LocalVariableName::Local(
                impl_variable,
            )))),
            function: Box::new(Rvalue::Move(Place::new(expr.variable))),
            target: LocalVariableName::Local(result_variable),
            return_type,
            argument_type,
        },
    });

    // Now, return the resultant expression.
    ExprGeneratedM {
        block: expr.block,
        variable: LocalVariableName::Local(result_variable),
    }
}

/// Searches the project index for a default implementation of the following aspect.
fn find_default_impl(
    project_index: &ProjectIndex,
    source_file: &SourceFileIdentifier,
    range: Range,
    name: &QualifiedName,
    parameters: Vec<Type>,
) -> DiagnosticResult<DefaultImpl> {
    let impls = project_index.default_impls(name);
    // Scan this list of default impls to see if any of them can work with this set of parameters.
    let mut candidates = impls
        .iter()
        .filter_map(|def_name| {
            let def = project_index.definition(def_name);
            // Can this definition be used to create an impl of the required type?
            // First, check its result type.
            let mut result_ty = &def.symbol_type;
            while let Type::Function(_, r) = result_ty {
                result_ty = r.deref();
                panic!("arguments in default impls not supported yet");
            }

            can_instance_as(
                result_ty,
                &Type::Impl {
                    name: name.clone(),
                    parameters: parameters.clone(),
                },
            )
            .map(|map| {
                // TODO: For now, just assume that the impl definition takes no arguments.
                DefaultImpl {
                    def_name: def_name.clone(),
                    type_params: def
                        .type_variables
                        .iter()
                        .map(|param| map[&param.name].clone())
                        .collect(),
                    params: Vec::new(),
                }
            })
        })
        .collect::<Vec<_>>();

    if candidates.is_empty() {
        DiagnosticResult::fail(ErrorMessage::new(
            format!(
                "did not find a default impl of type {}",
                Type::Impl {
                    name: name.clone(),
                    parameters
                }
            ),
            Severity::Error,
            Diagnostic::at(source_file, &range),
        ))
    } else if candidates.len() > 1 {
        DiagnosticResult::fail(ErrorMessage::new_with_many(
            format!(
                "found conflicting default impls of type {}",
                Type::Impl {
                    name: name.clone(),
                    parameters
                }
            ),
            Severity::Error,
            Diagnostic::at(source_file, &range),
            candidates
                .iter()
                .enumerate()
                .map(|(n, the_impl)| {
                    let def = project_index.definition(&the_impl.def_name);
                    HelpMessage {
                        message: format!("candidate #{}", n + 1),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(&the_impl.def_name.source_file, &def.name.range),
                    }
                })
                .collect(),
        ))
    } else {
        candidates.pop().unwrap().into()
    }
}

/// Can we instance this generic type by replacing type variables so that it matches the expected type?
/// If so, return the mapping of type variables to actual types.
/// TODO: add the mapping of borrow conditions, when borrow checking is fully implemented.
fn can_instance_as(generic: &Type, expected: &Type) -> Option<BTreeMap<String, Type>> {
    match generic {
        Type::Named { name, parameters } => {
            if let Type::Named {
                name: name2,
                parameters: parameters2,
            } = expected
            {
                if name == name2 {
                    let maps = parameters
                        .iter()
                        .zip(parameters2)
                        .map(|(generic, expected)| can_instance_as(generic, expected))
                        .collect::<Vec<_>>();
                    if maps.iter().any(|opt| opt.is_none()) {
                        None
                    } else {
                        unify_if_possible(maps.into_iter().map(|opt| opt.unwrap()).collect())
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
        Type::Variable { variable, .. } => Some({
            // TODO: what to do with the higher kinded parameters?
            let mut map = BTreeMap::new();
            map.insert(variable.clone(), expected.clone());
            map
        }),
        Type::Function(l, r) => {
            if let Type::Function(l2, r2) = expected {
                unify_if_possible(vec![can_instance_as(l, l2)?, can_instance_as(r, r2)?])
            } else {
                None
            }
        }
        ty @ Type::Primitive(_) => {
            if ty == expected {
                Some(BTreeMap::new())
            } else {
                None
            }
        }
        Type::Borrow { ty, .. } => {
            if let Type::Borrow { ty: ty2, .. } = expected {
                can_instance_as(ty, ty2)
            } else {
                None
            }
        }
        Type::Impl { name, parameters } => {
            if let Type::Impl {
                name: name2,
                parameters: parameters2,
            } = expected
            {
                if name == name2 {
                    let maps = parameters
                        .iter()
                        .zip(parameters2)
                        .map(|(generic, expected)| can_instance_as(generic, expected))
                        .collect::<Vec<_>>();
                    if maps.iter().any(|opt| opt.is_none()) {
                        None
                    } else {
                        unify_if_possible(maps.into_iter().map(|opt| opt.unwrap()).collect())
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
}

fn unify_if_possible(maps: Vec<BTreeMap<String, Type>>) -> Option<BTreeMap<String, Type>> {
    let mut result = BTreeMap::new();
    for map in maps {
        for (k, v) in map {
            match result.entry(k) {
                Entry::Vacant(vacant) => {
                    vacant.insert(v);
                }
                Entry::Occupied(occupied) => {
                    if v != *occupied.get() {
                        return None;
                    }
                }
            }
        }
    }
    Some(result)
}
