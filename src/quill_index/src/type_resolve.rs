//! Resolves an unqualified name into a fully qualified name with type information.
//! Use this for the intermediate type index, not for the main index.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::atomic::{AtomicU64, Ordering},
};

use either::Either;
use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_parser::{identifier::IdentifierP, types::TypeP};
use quill_type::{BorrowCondition, Lifetime, PrimitiveType, Type};

use crate::ForeignItemDeclarationC;

/// An unknown type, used for intermediate values of expressions that we don't know the type of.
/// To generate a new type variable, call `default`.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct TypeVariableId(u64);
static TYPE_VARIABLE_ID_GENERATOR: AtomicU64 = AtomicU64::new(0);

impl Default for TypeVariableId {
    fn default() -> Self {
        Self(TYPE_VARIABLE_ID_GENERATOR.fetch_add(1, Ordering::Relaxed))
    }
}

/// Resolves a type into a fully qualified type, given a list of the current
/// type parameters. For instance, if we are inside a data declaration `data Foo[T]`, then
/// the parameter `T` is in this list of type parameters.
pub(crate) fn resolve_typep(
    source_file: &SourceFileIdentifier,
    typep: &TypeP,
    type_params: &BTreeSet<String>,
    visible_types_and_aspects: &BTreeMap<&str, ForeignItemDeclarationC<'_>>,
) -> DiagnosticResult<Type> {
    match typep {
        TypeP::Named { identifier, params } => params
            .iter()
            .map(|arg| resolve_typep(source_file, arg, type_params, visible_types_and_aspects))
            .collect::<DiagnosticResult<Vec<_>>>()
            .bind(|parameters| {
                if identifier.segments.len() == 1
                    && type_params.contains(&identifier.segments[0].name)
                {
                    DiagnosticResult::ok(Type::Variable {
                        variable: identifier.segments[0].name.clone(),
                        parameters,
                    })
                } else {
                    resolve_type_identifier(
                        source_file,
                        identifier,
                        visible_types_and_aspects,
                        parameters,
                        None,
                    )
                }
            }),
        TypeP::Function(left, right) => {
            resolve_typep(source_file, left, type_params, visible_types_and_aspects).bind(|left| {
                resolve_typep(source_file, right, type_params, visible_types_and_aspects)
                    .map(|right| Type::Function(Box::new(left), Box::new(right)))
            })
        }
        TypeP::Borrow { ty, borrow } => {
            resolve_typep(source_file, &*ty, type_params, visible_types_and_aspects).map(|ty| {
                Type::Borrow {
                    ty: Box::new(ty),
                    borrow: Some(BorrowCondition {
                        lifetime: Lifetime {
                            name: borrow.lifetime.name.name.clone(),
                        },
                    }),
                }
            })
        }
        TypeP::Impl {
            impl_token,
            aspect,
            params,
        } => {
            let params = params
                .iter()
                .map(|ty| resolve_typep(source_file, ty, type_params, visible_types_and_aspects))
                .collect::<DiagnosticResult<Vec<_>>>();
            params.bind(|params| {
                resolve_type_identifier(
                    source_file,
                    aspect,
                    visible_types_and_aspects,
                    params,
                    Some(*impl_token),
                )
            })
        }
    }
}

/// If `impl_token` is not None, we're expecting the name of an aspect, not the name of a data type,
/// because we had the `impl` token before the name of this type.
pub(crate) fn resolve_type_identifier(
    source_file: &SourceFileIdentifier,
    identifier: &IdentifierP,
    visible_types_and_aspects: &BTreeMap<&str, ForeignItemDeclarationC<'_>>,
    parameters: Vec<Type>,
    impl_token: Option<Range>,
) -> DiagnosticResult<Type> {
    // First, check if this identifier matches a primitive type. These are always searched first.
    if identifier.segments.len() == 1 {
        if let Some(primitive_type) = match identifier.segments[0].name.as_str() {
            "Unit" => Some(PrimitiveType::Unit),
            "Bool" => Some(PrimitiveType::Bool),
            "Int" => Some(PrimitiveType::Int),
            _ => None,
        } {
            if parameters.is_empty() {
                return DiagnosticResult::ok(Type::Primitive(primitive_type));
            } else {
                return DiagnosticResult::ok_with(
                    Type::Primitive(primitive_type),
                    ErrorMessage::new(
                        "type parameters are not allowed on primitive types".to_string(),
                        Severity::Error,
                        Diagnostic::at(source_file, identifier),
                    ),
                );
            }
        }
    }

    // For now let's just deal with unqualified identifiers.
    match visible_types_and_aspects.get(identifier.segments[0].name.as_str()) {
        Some(type_decl) => match &type_decl.decl.ty {
            Either::Left(_ty) => {
                let result = Type::Named {
                    name: QualifiedName {
                        source_file: type_decl.source_file.clone(),
                        name: type_decl.decl.name.name.clone(),
                        range: type_decl.decl.name.range,
                    },
                    parameters,
                };

                if let Some(impl_token) = impl_token {
                    DiagnosticResult::ok_with(
                        result,
                        ErrorMessage::new_with(
                            "expected an aspect name, but this was a type name".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, identifier),
                            HelpMessage {
                                message: "try removing the `impl` keyword".to_string(),
                                help_type: HelpType::Help,
                                diagnostic: Diagnostic::at(source_file, &impl_token),
                            },
                        ),
                    )
                } else {
                    DiagnosticResult::ok(result)
                }
            }
            Either::Right(_asp) => {
                let result = Type::Impl {
                    name: QualifiedName {
                        source_file: type_decl.source_file.clone(),
                        name: type_decl.decl.name.name.clone(),
                        range: type_decl.decl.name.range,
                    },
                    parameters,
                };

                if impl_token.is_some() {
                    DiagnosticResult::ok(result)
                } else {
                    DiagnosticResult::ok_with(
                        result,
                        ErrorMessage::new_with(
                            "expected a type name, but this was an aspect name".to_string(),
                            Severity::Error,
                            Diagnostic::at(source_file, identifier),
                            HelpMessage {
                                message: "try adding the `impl` keyword before the aspect name"
                                    .to_string(),
                                help_type: HelpType::Help,
                                diagnostic: Diagnostic::at(source_file, &{
                                    let mut start = identifier.range().start;
                                    start.col = start.col.saturating_sub(1);
                                    Range::from(start)
                                }),
                            },
                        ),
                    )
                }
            }
        },
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from("could not resolve type"),
            Severity::Error,
            Diagnostic::at(source_file, &identifier.range()),
        )),
    }
}
