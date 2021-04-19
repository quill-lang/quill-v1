//! Resolves an unqualified name into a fully qualified name with type information.
//! Use this for the intermediate type index, not for the main index.

use std::{
    collections::{HashMap, HashSet},
    sync::atomic::{AtomicU64, Ordering},
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_parser::{IdentifierP, TypeP};
use quill_type::{PrimitiveType, Type};

use crate::ForeignTypeDeclarationC;

/// An unknown type, used for intermediate values of expressions that we don't know the type of.
/// To generate a new type variable, call `default`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
    type_params: &HashSet<String>,
    visible_types: &HashMap<&str, ForeignTypeDeclarationC<'_>>,
) -> DiagnosticResult<Type> {
    match typep {
        TypeP::Named { identifier, params } => params
            .iter()
            .map(|arg| resolve_typep(source_file, arg, type_params, visible_types))
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
                    resolve_type_identifier(source_file, identifier, visible_types, parameters)
                }
            }),
        TypeP::Function(left, right) => {
            resolve_typep(source_file, &left, type_params, visible_types).bind(|left| {
                resolve_typep(source_file, &right, type_params, visible_types)
                    .map(|right| Type::Function(Box::new(left), Box::new(right)))
            })
        }
    }
}

pub(crate) fn resolve_type_identifier(
    source_file: &SourceFileIdentifier,
    identifier: &IdentifierP,
    visible_types: &HashMap<&str, ForeignTypeDeclarationC<'_>>,
    parameters: Vec<Type>,
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
    match visible_types.get(identifier.segments[0].name.as_str()) {
        Some(type_decl) => DiagnosticResult::ok(Type::Named {
            name: QualifiedName {
                source_file: type_decl.source_file.clone(),
                name: type_decl.decl.name.name.clone(),
                range: type_decl.decl.name.range,
            },
            parameters,
        }),
        None => DiagnosticResult::fail(ErrorMessage::new(
            String::from("could not resolve type"),
            Severity::Error,
            Diagnostic::at(source_file, &identifier.range()),
        )),
    }
}
