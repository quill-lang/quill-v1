use std::collections::BTreeMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_parser::{definition::DefinitionBodyP, expr_pat::ExprPatP};
use quill_type::Type;

use crate::{
    hir::{
        expr::{Expression, ExpressionContents, ExpressionContentsT, ExpressionT, TypeVariable},
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
) -> DiagnosticResult<Expression> {
    let range = expr.range();
    let ExpressionT {
        type_variable,
        contents,
        ..
    } = expr;

    let (ty, mut messages) =
        substitute_type(substitution, type_variable.into(), source_file, range).destructure();

    // We only want to generate one error message, all the others will just say "could not deduce type of expression".
    messages.truncate(1);
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
        )
        .bind(|contents| DiagnosticResult::ok_with_many(Expression { ty, contents }, messages)),
        None => DiagnosticResult::fail_many(messages),
    }
}

/// `ty` is the type of `contents`.
fn substitute_contents(
    substitution: &BTreeMap<TypeVariableId, TypeVariable>,
    contents: ExpressionContentsT,
    ty: &Type,
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
) -> DiagnosticResult<ExpressionContents> {
    match contents {
        ExpressionContentsT::Argument(a) => DiagnosticResult::ok(ExpressionContents::Argument(a)),
        ExpressionContentsT::Local(a) => DiagnosticResult::ok(ExpressionContents::Local(a)),
        ExpressionContentsT::Symbol {
            name,
            range,
            type_variables,
        } => {
            // Check that all the type variables for this symbol are known.
            let type_variables = type_variables
                .iter()
                .map(|(ty_name, ty_id)| {
                    let (ty, messages) =
                        substitute_type(substitution, ty_id.clone(), source_file, range)
                            .destructure();
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
            type_variables.map(|type_variables| ExpressionContents::Symbol {
                name,
                range,
                type_variables,
            })
        }
        ExpressionContentsT::Apply(l, r) => {
            substitute(substitution, *l, source_file, project_index, visible_names).bind(|l| {
                substitute(substitution, *r, source_file, project_index, visible_names)
                    .map(|r| ExpressionContents::Apply(Box::new(l), Box::new(r)))
            })
        }
        ExpressionContentsT::Lambda {
            lambda_token,
            params,
            expr,
        } => substitute(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
        )
        .bind(|expr| {
            params
                .into_iter()
                .map(|(name, ty)| {
                    substitute_type(substitution, ty, source_file, name.range).map(|ty| (name, ty))
                })
                .collect::<DiagnosticResult<_>>()
                .map(|params| ExpressionContents::Lambda {
                    lambda_token,
                    params,
                    expr: Box::new(expr),
                })
        }),
        ExpressionContentsT::Let {
            let_token,
            name,
            expr,
        } => substitute(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
        )
        .map(|expr| ExpressionContents::Let {
            let_token,
            name,
            expr: Box::new(expr),
        }),
        ExpressionContentsT::Block {
            open_bracket,
            close_bracket,
            statements,
        } => statements
            .into_iter()
            .map(|stmt| {
                substitute(
                    substitution,
                    stmt,
                    source_file,
                    project_index,
                    visible_names,
                )
            })
            .collect::<DiagnosticResult<_>>()
            .map(|statements| ExpressionContents::Block {
                open_bracket,
                close_bracket,
                statements,
            }),
        ExpressionContentsT::ConstructData {
            data_type_name,
            variant,
            fields,
            open_brace,
            close_brace,
        } => fields
            .into_iter()
            .map(|(field_name, field_expr)| {
                substitute(
                    substitution,
                    field_expr,
                    source_file,
                    project_index,
                    visible_names,
                )
                .map(|field_expr| (field_name, field_expr))
            })
            .collect::<DiagnosticResult<_>>()
            .map(|fields| ExpressionContents::ConstructData {
                data_type_name,
                variant,
                fields,
                open_brace,
                close_brace,
            }),
        ExpressionContentsT::ConstantValue { value, range } => {
            DiagnosticResult::ok(ExpressionContents::ConstantValue { value, range })
        }
        ExpressionContentsT::Borrow { borrow_token, expr } => substitute(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
        )
        .map(|expr| ExpressionContents::Borrow {
            borrow_token,
            expr: Box::new(expr),
        }),
        ExpressionContentsT::Copy { copy_token, expr } => substitute(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
        )
        .map(|expr| ExpressionContents::Copy {
            copy_token,
            expr: Box::new(expr),
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
            )
        }
        ExpressionContentsT::Match {
            match_token,
            expr,
            cases,
        } => substitute(
            substitution,
            *expr,
            source_file,
            project_index,
            visible_names,
        )
        .bind(|expr| {
            cases
                .into_iter()
                .map(|(pattern, replacement)| {
                    substitute(
                        substitution,
                        replacement,
                        source_file,
                        project_index,
                        visible_names,
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
                .map(|cases| ExpressionContents::Match {
                    match_token,
                    expr: Box::new(expr),
                    cases,
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

fn typeck_impl(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    impl_token: Range,
    aspect: &QualifiedName,
    parameters: &[Type],
    body: DefinitionBodyP,
    visible_names: &VisibleNames,
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

    typeck.compute_impl(impl_token, aspect, parameters, cases, visible_names)
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
