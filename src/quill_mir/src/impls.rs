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
    mir::{LocalVariableInfo, LocalVariableName, Place, Rvalue, Statement, StatementKind},
};

/// A definition that can be invoked to yield a default impl for an aspect.
struct DefaultImpl {
    def_name: QualifiedName,
    type_params: Vec<Type>,
    params: Vec<DefaultImpl>,
}

/// Given an expression (a function taking an impl), and an impl type (the parameter),
/// find a relevant default impl and apply it to the expression.
pub(crate) fn find_and_apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    name: &QualifiedName,
    parameters: &[Type],
    expr: &ExprGeneratedM,
) -> DiagnosticResult<ImplGeneratedM> {
    find_default_impl(ctx.project_index, ctx.source_file, range, name, parameters)
        .map(|default_impl| apply_default_impl(ctx, range, expr.variable, default_impl))
}

/// Like an ExprGeneratedM but allows us to merge statements into a single block.
pub(crate) struct ImplGeneratedM {
    pub(crate) statements: Vec<Statement>,
    pub(crate) variable: LocalVariableName,
}

fn apply_default_impl(
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    expr: LocalVariableName,
    default_impl: DefaultImpl,
) -> ImplGeneratedM {
    let def = ctx.project_index.definition(&default_impl.def_name);

    let argument_type = replace_type_variables(
        def.symbol_type.clone(),
        &def.type_variables,
        &default_impl.type_params,
    );
    let return_type = if let Type::Function(_, r) = &ctx.locals[&expr].ty {
        r.deref().clone()
    } else {
        unreachable!()
    };

    let mut impl_variable = LocalVariableName::Local(ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: argument_type,
        name: None,
    }));

    let result_variable = ctx.new_local_variable(LocalVariableInfo {
        range,
        ty: return_type,
        name: None,
    });

    let mut statements = vec![
        // Instance the impl.
        Statement {
            range,
            kind: StatementKind::InstanceSymbol {
                name: default_impl.def_name,
                type_variables: default_impl.type_params,
                target: impl_variable,
            },
        },
    ];

    // Apply the arguments.
    for param in default_impl.params.into_iter() {
        // Apply the argument to the impl.
        let result = apply_default_impl(ctx, range, impl_variable, param);
        impl_variable = result.variable;
        statements.extend(result.statements);
    }

    // Apply the impl to the expr.
    statements.push(Statement {
        range,
        kind: StatementKind::Apply {
            argument: Box::new(Rvalue::Move(Place::new(impl_variable))),
            function: Box::new(Rvalue::Move(Place::new(expr))),
            target: LocalVariableName::Local(result_variable),
        },
    });

    // Now, return the resultant expression.
    ImplGeneratedM {
        statements,
        variable: LocalVariableName::Local(result_variable),
    }
}

/// Searches the project index for a default implementation of the following aspect.
/// TODO: We need to perform a number of checks:
///     - check for recursive impls so we don't stack overflow
///     - add better error messages for conflicting required impls
fn find_default_impl(
    project_index: &ProjectIndex,
    source_file: &SourceFileIdentifier,
    range: Range,
    name: &QualifiedName,
    parameters: &[Type],
) -> DiagnosticResult<DefaultImpl> {
    let mut candidates =
        find_default_impl_candidates(project_index, source_file, range, name, parameters);

    if candidates.is_empty() {
        DiagnosticResult::fail(ErrorMessage::new(
            format!(
                "did not find a default impl of type {}",
                Type::Impl {
                    name: name.clone(),
                    parameters: parameters.to_vec()
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
                    parameters: parameters.to_vec()
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

/// `name` and `parameters` are the name and type parameters for the aspect we're finding a default impl for.
fn find_default_impl_candidates(
    project_index: &ProjectIndex,
    source_file: &SourceFileIdentifier,
    range: Range,
    name: &QualifiedName,
    parameters: &[Type],
) -> Vec<DefaultImpl> {
    let impls = project_index.default_impls(name);
    // Scan this list of default impls to see if any of them can work with this set of parameters.
    impls
        .iter()
        .filter_map(|def_name| {
            let def = project_index.definition(def_name);
            // Can this definition be used to create an impl of the required type?
            // First, check its result type.
            let mut required_impls = Vec::new();
            let mut result_ty = &def.symbol_type;
            while let Type::Function(l, r) = result_ty {
                required_impls.push(l.deref());
                result_ty = r.deref();
            }

            can_instance_as(
                result_ty,
                &Type::Impl {
                    name: name.clone(),
                    parameters: parameters.to_vec(),
                },
            )
            .and_then(|map| {
                // Check if all the requirements are satisfied.
                // First, let's compute all the type variables in this definition.
                let concrete_type_parameters = def
                    .type_variables
                    .iter()
                    .map(|named| map.get(&named.name))
                    .collect::<Vec<_>>();
                if concrete_type_parameters.iter().any(|val| val.is_none()) {
                    return None;
                }
                let concrete_type_parameters = concrete_type_parameters
                    .into_iter()
                    .map(|val| val.unwrap().clone())
                    .collect::<Vec<_>>();

                let mut inner_impls = Vec::new();
                for required in required_impls {
                    let (inner_name, inner_parameters) =
                        if let Type::Impl { name, parameters } = required {
                            (name, parameters.deref())
                        } else {
                            unreachable!()
                        };
                    let mut inner_candidates = find_default_impl_candidates(
                        project_index,
                        source_file,
                        range,
                        inner_name,
                        &inner_parameters
                            .iter()
                            .map(|ty| {
                                replace_type_variables(
                                    ty.clone(),
                                    &def.type_variables,
                                    &concrete_type_parameters,
                                )
                            })
                            .collect::<Vec<_>>(),
                    );
                    if inner_candidates.is_empty() {
                        return None;
                    }
                    if inner_candidates.len() > 1 {
                        // TODO: this will give a really bad error message - saying we have no impl instead of two conflicting impls
                        return None;
                    }
                    inner_impls.push(inner_candidates.pop().unwrap());
                }

                Some(DefaultImpl {
                    def_name: def_name.clone(),
                    type_params: def
                        .type_variables
                        .iter()
                        .map(|param| map[&param.name].clone())
                        .collect(),
                    params: inner_impls,
                })
            })
        })
        .collect::<Vec<_>>()
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
