use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, Severity},
    location::SourceFileIdentifier,
};

use crate::expr_pat::ExprPatP;

/// Ensure that certain malformed expressions are not forwarded into subsequent parse steps.
pub(crate) fn validate(source_file: &SourceFileIdentifier, expr: &ExprPatP) -> Vec<ErrorMessage> {
    let mut messages = Vec::new();
    messages.extend(validate_expr_types(
        source_file,
        expr,
        ValidTypes {
            let_expr: Some(TypeInvalidReason {
                produce_error_message: Box::new(|expr| {
                    ErrorMessage::new(
                "`let` statements can't be used as top-level expressions, since `let` expressions always produce the unit value".to_string(),
                        Severity::Error,
                        Diagnostic::at(source_file, expr)
                    )
                }),
            }),
        },
    ));
    messages
}

/// Why was a specific expression type invalid in this location?
struct TypeInvalidReason<'a> {
    produce_error_message: Box<dyn FnOnce(&ExprPatP) -> ErrorMessage + 'a>,
}

struct ValidTypes<'a> {
    let_expr: Option<TypeInvalidReason<'a>>,
}

/// What types of expressions are valid here?
/// Fixes #54, #76.
fn validate_expr_types<'a>(
    source_file: &'a SourceFileIdentifier,
    expr: &ExprPatP,
    valid_types: ValidTypes<'a>,
) -> Vec<ErrorMessage> {
    match expr {
        ExprPatP::Let { expr: inner, .. } => {
            if let Some(reason) = valid_types.let_expr {
                vec![(reason.produce_error_message)(expr)]
            } else {
                validate_expr_types(
                    source_file,
                    inner,
                    ValidTypes {
                        let_expr: Some(TypeInvalidReason {
                            produce_error_message: Box::new(|expr| {
                                ErrorMessage::new(
                            "`let` statements can't be nested, since `let` expressions always produce the unit value".to_string(),
                                    Severity::Error,
                                    Diagnostic::at(source_file, expr)
                                )
                            }),
                        }),
                    },
                )
            }
        }
        ExprPatP::Block { statements, .. } => {
            let (last, others) = statements.split_last().unwrap();
            others
                .iter()
                .map(|expr| validate_expr_types(source_file, expr, ValidTypes { let_expr: None }))
                .flatten()
                .chain(validate_expr_types(
                    source_file,
                    last,
                    ValidTypes {
                        let_expr: Some(TypeInvalidReason {
                            produce_error_message: Box::new(|expr| {
                                ErrorMessage::new(
                                    "`let` statements can't be the last expression in a block"
                                        .to_string(),
                                    Severity::Error,
                                    Diagnostic::at(source_file, expr),
                                )
                            }),
                        }),
                    },
                ))
                .collect()
        }
        ExprPatP::Unknown(_) => {
            vec![ErrorMessage::new(
                String::from("underscore not allowed in expressions"),
                Severity::Error,
                Diagnostic::at(source_file, expr),
            )]
        }
        ExprPatP::Apply(l, r) => {
            let mut l = validate_expr_types(
                source_file,
                l,
                ValidTypes {
                    let_expr: Some(TypeInvalidReason {
                        produce_error_message: Box::new(|expr| {
                            ErrorMessage::new(
                                "`let` statements can't be used in function application"
                                    .to_string(),
                                Severity::Error,
                                Diagnostic::at(source_file, expr),
                            )
                        }),
                    }),
                },
            );
            let r = validate_expr_types(
                source_file,
                r,
                ValidTypes {
                    let_expr: Some(TypeInvalidReason {
                        produce_error_message: Box::new(|expr| {
                            ErrorMessage::new(
                                "`let` statements can't be used in function application"
                                    .to_string(),
                                Severity::Error,
                                Diagnostic::at(source_file, expr),
                            )
                        }),
                    }),
                },
            );
            l.extend(r);
            l
        }
        ExprPatP::Lambda { expr, .. } => validate_expr_types(
            source_file,
            &*expr,
            ValidTypes {
                let_expr: Some(TypeInvalidReason {
                    produce_error_message: Box::new(|expr| {
                        ErrorMessage::new(
                            "`let` statements can't be used in function application".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, expr),
                        )
                    }),
                }),
            },
        ),
        ExprPatP::Borrow { expr, .. } => validate_expr_types(
            source_file,
            &*expr,
            ValidTypes {
                let_expr: Some(TypeInvalidReason {
                    produce_error_message: Box::new(|expr| {
                        ErrorMessage::new(
                            "`let` statements can't be used in function application".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, expr),
                        )
                    }),
                }),
            },
        ),
        ExprPatP::Copy { expr, .. } => validate_expr_types(
            source_file,
            &*expr,
            ValidTypes {
                let_expr: Some(TypeInvalidReason {
                    produce_error_message: Box::new(|expr| {
                        ErrorMessage::new(
                            "`let` statements can't be used in function application".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, expr),
                        )
                    }),
                }),
            },
        ),
        ExprPatP::ConstructData { fields, .. } => fields
            .fields
            .iter()
            .map(|(_field_name, expr)| {
                validate_expr_types(
                    source_file,
                    expr,
                    ValidTypes {
                        let_expr: Some(TypeInvalidReason {
                            produce_error_message: Box::new(|expr| {
                                ErrorMessage::new(
                                    "`let` statements can't be used in constructor fields"
                                        .to_string(),
                                    Severity::Error,
                                    Diagnostic::at(source_file, expr),
                                )
                            }),
                        }),
                    },
                )
            })
            .flatten()
            .collect(),
        _ => Vec::new(),
    }
}
