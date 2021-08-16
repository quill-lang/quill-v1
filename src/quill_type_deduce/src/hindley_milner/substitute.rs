use std::collections::BTreeMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_parser::{definition::DefinitionBodyP, expr_pat::ExprPatP, identifier::NameP};
use quill_type::Type;

use crate::{
    hir::{
        expr::{
            BoundVariable, Expression, ExpressionContents, ExpressionContentsT, ExpressionT,
            TypeVariable,
        },
        pattern::Pattern,
    },
    type_check::{TypeChecker, TypeVariablePrinter, VisibleNames},
    type_resolve::TypeVariableId,
};

/// Apply the given type variable substitution to this expression.
/// This should replace all unknown types with known types, if the type check succeeded.
pub(crate) fn substitute(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    expr: ExpressionT,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    args: &BTreeMap<String, BoundVariable>,
) -> DiagnosticResult<Expression> {
    // Generate a list of arguments to the function.
    let visible_local_names = args
        .iter()
        .map(|(name, bound_variable)| {
            (
                NameP {
                    name: name.clone(),
                    range: expr.range(),
                },
                LocalName {
                    location: LocalVariableLocation::Argument,
                    ty: bound_variable.var_type.clone(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();

    substitute_outer(
        substitution,
        expr,
        source_file,
        project_index,
        visible_names,
        &visible_local_names,
    )
}

fn substitute_outer(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    expr: ExpressionT,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    visible_local_names: &VisibleLocalNames,
) -> DiagnosticResult<Expression> {
    substitute_inner(
        substitution,
        expr,
        source_file,
        project_index,
        visible_names,
        visible_local_names,
    )
    .map(|(substituted, ty)| Expression {
        ty,
        contents: substituted.expr,
    })
}

fn substitute_inner(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    expr: ExpressionT,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    visible_local_names: &VisibleLocalNames,
) -> DiagnosticResult<(SubstitutedExpression, Type)> {
    let range = expr.range();
    let ExpressionT {
        type_variable,
        contents,
        ..
    } = expr;

    let (ty, mut messages) =
        substitute_type(substitution, type_variable.into(), source_file, range).destructure();

    // We only want to generate one error message, all the others will just say "could not deduce type of expression".
    // TODO: is this actually true? and anyway, don't we still want to know which expression types are not known?
    // messages.truncate(1);

    if let Some(message) = messages.get_mut(0) {
        if message.help.is_empty() {
            let mut tvp = TypeVariablePrinter::new(substitution.clone());
            message.help.push(HelpMessage {
                message: format!(
                    "best guess of expression type was {}",
                    tvp.print(type_variable.into())
                ),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, &range),
            })
        }
    }

    match ty {
        Some(ty) => substitute_contents(
            substitution,
            contents,
            &ty,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .bind(|contents| DiagnosticResult::ok_with_many((contents, ty), messages)),
        None => DiagnosticResult::fail_many(messages),
    }
}

pub(crate) type VisibleLocalNames = BTreeMap<NameP, LocalName>;

#[derive(Debug, Clone)]
pub(crate) struct LocalName {
    location: LocalVariableLocation,
    pub(crate) ty: Type,
}

/// Where was a local variable defined?
#[derive(Debug, Copy, Clone)]
pub(crate) enum LocalVariableLocation {
    Argument,
    Local,
}

/// A substituted expression, along with a map detailing the local variables visible after this expression was executed,
/// e.g. variables declared in `let` expressions and arguments to the function.
struct SubstitutedExpression {
    expr: ExpressionContents,
    extra_names: VisibleLocalNames,
}

impl From<ExpressionContents> for SubstitutedExpression {
    fn from(expr: ExpressionContents) -> Self {
        Self {
            expr,
            extra_names: VisibleLocalNames::new(),
        }
    }
}

/// `ty` is the expected type of `contents`, after type coercion (eliding impls, for example).
/// Type coercion is implemented in the MIR translation phase.
fn substitute_contents(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    contents: ExpressionContentsT,
    ty: &Type,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    visible_local_names: &VisibleLocalNames,
) -> DiagnosticResult<SubstitutedExpression> {
    match contents {
        ExpressionContentsT::Local(a) => DiagnosticResult::ok(ExpressionContents::Local(a).into()),
        ExpressionContentsT::Symbol {
            name,
            range,
            type_variables,
        } => {
            // Reorder the type variables so they're in the correct order for this symbol.
            let expected_type_variable_order = &project_index.definition(&name).type_variables;
            let mut type_variables = type_variables.into_iter().collect::<Vec<_>>();
            type_variables.sort_by(|(name1, _), (name2, _)| {
                // Compare their positions in the expected type variable order.
                let pos1 = expected_type_variable_order
                    .iter()
                    .position(|param| param.name == *name1)
                    .unwrap();
                let pos2 = expected_type_variable_order
                    .iter()
                    .position(|param| param.name == *name2)
                    .unwrap();
                pos1.cmp(&pos2)
            });

            // Check that all the type variables for this symbol are known.
            let type_variables = type_variables
                .into_iter()
                .map(|(ty_name, ty_id)| {
                    let (ty, messages) =
                        substitute_type(substitution, ty_id, source_file, range).destructure();
                    // The error message, if present, needs to be customised to state that the problem is with the type variable.
                    if let Some(ty) = ty {
                        DiagnosticResult::ok_with_many(ty, messages)
                    } else {
                        DiagnosticResult::fail(ErrorMessage::new(
                            format!(
                                "type variable {} from {} could not be deduced",
                                ty_name, name
                            ),
                            Severity::Error,
                            Diagnostic::at(source_file, &range),
                        ))
                    }
                })
                .collect::<DiagnosticResult<Vec<Type>>>();
            type_variables.map(|type_variables| {
                ExpressionContents::Symbol {
                    name,
                    range,
                    type_variables,
                }
                .into()
            })
        }
        ExpressionContentsT::Apply(l, r) => substitute_outer(
            substitution,
            *l,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .bind(|l| {
            {
                substitute_outer(
                    substitution,
                    *r,
                    source_file,
                    project_index,
                    visible_names,
                    visible_local_names,
                )
                .map(|r| ExpressionContents::Apply(Box::new(l), Box::new(r)).into())
            }
        }),
        ExpressionContentsT::Lambda {
            lambda_token,
            params,
            expr,
        } => params
            .into_iter()
            .map(|(name, ty)| {
                substitute_type(substitution, ty, source_file, name.range).map(|ty| (name, ty))
            })
            .collect::<DiagnosticResult<_>>()
            .bind(|params| {
                substitute_outer(
                    substitution,
                    *expr,
                    source_file,
                    project_index,
                    visible_names,
                    &{
                        let mut locals = visible_local_names.clone();
                        locals.extend(params.iter().map(|(param_name, param_ty)| {
                            (
                                param_name.clone(),
                                LocalName {
                                    location: LocalVariableLocation::Local,
                                    ty: param_ty.clone(),
                                },
                            )
                        }));
                        locals
                    },
                )
                .map(|expr| {
                    ExpressionContents::Lambda {
                        lambda_token,
                        params,
                        expr: Box::new(expr),
                    }
                    .into()
                })
            }),
        ExpressionContentsT::Let {
            let_token,
            name,
            expr,
        } => substitute_outer(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .map(|expr| {
            let mut extra_names = VisibleLocalNames::new();
            extra_names.insert(
                name.clone(),
                LocalName {
                    location: LocalVariableLocation::Local,
                    ty: expr.ty.clone(),
                },
            );
            SubstitutedExpression {
                expr: ExpressionContents::Let {
                    let_token,
                    name,
                    expr: Box::new(expr),
                },
                extra_names,
            }
        }),
        ExpressionContentsT::Block {
            open_bracket,
            close_bracket,
            statements,
        } => {
            let mut visible_local_names = visible_local_names.clone();
            let mut statements_collated = Vec::new();
            let mut messages = Vec::new();
            for stmt in statements {
                let (stmt, more_messages) = substitute_inner(
                    substitution,
                    stmt,
                    source_file,
                    project_index,
                    visible_names,
                    &visible_local_names,
                )
                .destructure();
                if let Some((substituted, ty)) = stmt {
                    statements_collated.push(Expression {
                        ty,
                        contents: substituted.expr,
                    });
                    visible_local_names.extend(substituted.extra_names);
                }
                messages.extend(more_messages);
            }

            DiagnosticResult::ok_with_many(
                ExpressionContents::Block {
                    open_bracket,
                    close_bracket,
                    statements: statements_collated,
                }
                .into(),
                messages,
            )
        }
        ExpressionContentsT::ConstructData {
            data_type_name,
            variant,
            fields,
            open_brace,
            close_brace,
        } => fields
            .into_iter()
            .map(|(field_name, field_expr)| {
                substitute_outer(
                    substitution,
                    field_expr,
                    source_file,
                    project_index,
                    visible_names,
                    visible_local_names,
                )
                .map(|field_expr| (field_name, field_expr))
            })
            .collect::<DiagnosticResult<_>>()
            .map(|fields| {
                ExpressionContents::ConstructData {
                    data_type_name,
                    variant,
                    fields,
                    open_brace,
                    close_brace,
                }
                .into()
            }),
        ExpressionContentsT::ConstantValue { value, range } => {
            DiagnosticResult::ok(ExpressionContents::ConstantValue { value, range }.into())
        }
        ExpressionContentsT::Borrow { borrow_token, expr } => substitute_outer(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .map(|expr| {
            ExpressionContents::Borrow {
                borrow_token,
                expr: Box::new(expr),
            }
            .into()
        }),
        ExpressionContentsT::Copy { copy_token, expr } => substitute_outer(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .map(|expr| {
            ExpressionContents::Copy {
                copy_token,
                expr: Box::new(expr),
            }
            .into()
        }),
        ExpressionContentsT::Impl {
            impl_token,
            implementations,
        } => {
            // Perform another round of type inference on the contents of this impl.
            // First, work out the exact type parameters on this impl.
            let (aspect, parameters) = if let Type::Impl { name, parameters } = ty {
                (name, parameters)
            } else {
                unreachable!()
            };

            typeck_impl(
                source_file,
                project_index,
                impl_token,
                aspect,
                parameters,
                implementations,
                visible_names,
                visible_local_names,
            )
            .map(|contents| contents.into())
        }
        ExpressionContentsT::Match {
            match_token,
            expr,
            cases,
        } => substitute_outer(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
            visible_local_names,
        )
        .bind(|expr| {
            cases
                .into_iter()
                .map(|(pattern, replacement)| {
                    substitute_outer(
                        substitution,
                        replacement,
                        source_file,
                        project_index,
                        visible_names,
                        visible_local_names,
                    )
                    .bind(|replacement| {
                        resolve_pattern(
                            &pattern,
                            &expr.ty,
                            source_file,
                            project_index,
                            visible_names,
                        )
                        .map(|pattern| (pattern, replacement))
                    })
                })
                .collect::<DiagnosticResult<Vec<_>>>()
                .map(|cases| {
                    ExpressionContents::Match {
                        match_token,
                        expr: Box::new(expr),
                        cases,
                    }
                    .into()
                })
        }),
    }
}

/// Verify that the pattern is of the given type, and then return it.
fn resolve_pattern(
    pat: &ExprPatP,
    ty: &Type,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
) -> DiagnosticResult<Pattern> {
    // Create a dummy type checker to use its functions.
    let typeck = TypeChecker {
        source_file,
        project_index,
        messages: Vec::new(),
    };
    typeck.resolve_type_pattern(visible_names, pat.clone(), ty.clone())
}

// It doesn't really make sense to try to simplify this function signature too much.
#[allow(clippy::too_many_arguments)]
fn typeck_impl(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    impl_token: Range,
    aspect: &QualifiedName,
    parameters: &[Type],
    body: DefinitionBodyP,
    visible_names: &VisibleNames,
    visible_local_names: &VisibleLocalNames,
) -> DiagnosticResult<ExpressionContents> {
    let cases = match body {
        DefinitionBodyP::PatternMatch(cases) => cases,
        DefinitionBodyP::CompilerIntrinsic(range) => {
            return DiagnosticResult::fail(ErrorMessage::new(
                "`compiler_intrinsic` not allowed in `impl` expressions".to_string(),
                Severity::Error,
                Diagnostic::at(source_file, &range),
            ));
        }
    };

    let aspect = project_index.aspect(aspect);

    let typeck = TypeChecker {
        source_file,
        project_index,
        messages: Vec::new(),
    };

    typeck.compute_impl(
        impl_token,
        aspect,
        parameters,
        cases,
        visible_names,
        visible_local_names,
    )
}

fn substitute_type(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    ty: TypeVariable,
    source_file: &SourceFileIdentifier,
    range: Range,
) -> DiagnosticResult<Type> {
    match ty {
        TypeVariable::Named { name, parameters } => {
            let parameters = parameters
                .into_iter()
                .map(|param| substitute_type(substitution, param, source_file, range))
                .collect::<DiagnosticResult<Vec<_>>>();
            parameters.map(|parameters| Type::Named { name, parameters })
        }
        TypeVariable::Function(l, r) => {
            substitute_type(substitution, *l, source_file, range).bind(|l| {
                substitute_type(substitution, *r, source_file, range)
                    .map(|r| Type::Function(Box::new(l), Box::new(r)))
            })
        }
        TypeVariable::Unknown { id } => match substitution.get(&id) {
            Some(value) => {
                // Sometimes, we can have a substitution that substitutes some type variable for itself.
                // The substitution is idempotent, so there are no cycles.
                // So we'll check if `value == TypeVariable::Unknown(id)`.
                if let TypeVariable::Unknown { id: other_id } = value {
                    if *other_id == id {
                        return DiagnosticResult::fail(ErrorMessage::new(
                            String::from("could not deduce type of this expression"),
                            Severity::Error,
                            Diagnostic::at(source_file, &range),
                        ));
                    }
                }

                substitute_type(substitution, value.clone(), source_file, range)
            }
            None => DiagnosticResult::fail(ErrorMessage::new(
                String::from("could not deduce type of this expression"),
                Severity::Error,
                Diagnostic::at(source_file, &range),
            )),
        },
        TypeVariable::Variable {
            variable,
            parameters,
        } => parameters
            .into_iter()
            .map(|param| substitute_type(substitution, param, source_file, range))
            .collect::<DiagnosticResult<_>>()
            .map(|parameters| Type::Variable {
                variable,
                parameters,
            }),
        TypeVariable::Primitive(prim) => DiagnosticResult::ok(Type::Primitive(prim)),
        TypeVariable::Borrow { ty } => {
            substitute_type(substitution, *ty, source_file, range).map(|ty| Type::Borrow {
                ty: Box::new(ty),
                borrow: None,
            })
        }
        TypeVariable::Impl { name, parameters } => {
            let parameters = parameters
                .into_iter()
                .map(|param| substitute_type(substitution, param, source_file, range))
                .collect::<DiagnosticResult<Vec<_>>>();
            parameters.map(|parameters| Type::Impl { name, parameters })
        }
    }
}
