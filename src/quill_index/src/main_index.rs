//! Computes an index of all top-level items in a module,
//! storing type information. The module index is sufficient to determine the type
//! of any expression.

use std::collections::{hash_map::Entry, HashMap, HashSet};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
};
use quill_parser::{FileP, NameP};
use quill_type::Type;

use crate::type_index::ProjectTypesC;

/// An index of all top-level items in a file.
///
/// Realistically this type should probably have the `I` suffix, but in my opinion it's pretty self-evident.
#[derive(Debug)]
pub struct FileIndex {
    pub types: HashMap<String, TypeDeclarationI>,
    pub definitions: HashMap<String, DefinitionI>,
    /// Maps enum variant names (True, Left) to the enum that contains them (Bool, Either)
    pub enum_variant_types: HashMap<String, String>,
}

pub type ProjectIndex = HashMap<SourceFileIdentifier, FileIndex>;

/// A type declaration, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct TypeDeclarationI {
    /// This is kept here mostly because it contains the `Range` where it was defined.
    pub name: NameP,
    pub decl_type: TypeDeclarationTypeI,
}

/// Either a data declaration, a new type wrapper, a type alias, or a dependent type.
#[derive(Debug)]
pub enum TypeDeclarationTypeI {
    Data(DataI),
    Enum(EnumI),
}

/// A `data` declaration.
#[derive(Debug)]
pub struct DataI {
    /// Where was this data declaration written?
    pub range: Range,
    pub type_params: Vec<TypeParameter>,
    pub type_ctor: TypeConstructorI,
}

/// A `enum` declaration.
#[derive(Debug)]
pub struct EnumI {
    /// Where was this enum declaration written?
    pub range: Range,
    pub type_params: Vec<TypeParameter>,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug)]
pub struct EnumVariant {
    pub name: NameP,
    pub type_ctor: TypeConstructorI,
}

#[derive(Debug)]
pub struct TypeConstructorI {
    pub fields: Vec<(NameP, Type)>,
}

/// A top-level definition, i.e. a `def` block.
/// TODO: In the future, we will need to add a list of constraints to definitions and data blocks.
#[derive(Debug)]
pub struct DefinitionI {
    pub name: NameP,
    pub type_variables: Vec<TypeParameter>,
    pub symbol_type: Type,
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub name: String,
    /// A type variable may have one or more unnamed parameters, e.g. `F[_]` is a common type for a functor.
    /// This field stores how many such parameters the type variable has.
    pub parameters: u32,
}

/// Returns a generic error message about multiply defined symbols, making sure that the "earlier" symbol
/// actually was the one that appeared earlier in the file.
fn name_used_earlier(
    source_file: &SourceFileIdentifier,
    range1: Range,
    range2: Range,
) -> ErrorMessage {
    ErrorMessage::new_with(
        String::from("this name was used earlier for another definition"),
        Severity::Error,
        Diagnostic::at(source_file, &range1.max(range2)),
        HelpMessage {
            message: String::from("previously used here"),
            help_type: HelpType::Note,
            diagnostic: Diagnostic::at(source_file, &range1.min(range2)),
        },
    )
}

/// Computes the index for a module.
pub fn index(
    source_file: &SourceFileIdentifier,
    file_parsed: &FileP,
    project_types: &ProjectTypesC,
) -> DiagnosticResult<FileIndex> {
    let mut messages = Vec::new();

    let mut types = HashMap::<String, TypeDeclarationI>::new();
    let mut definitions = HashMap::<String, DefinitionI>::new();
    let mut enum_variant_types = HashMap::<String, String>::new();

    for definition in &file_parsed.definitions {
        match definitions.entry(definition.name.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    definition.name.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add this definition into the map.
                let symbol_type = crate::type_resolve::resolve_typep(
                    source_file,
                    &definition.definition_type,
                    &definition
                        .type_parameters
                        .iter()
                        .map(|id| id.name.name.clone())
                        .collect(),
                    project_types,
                );
                let (symbol_type, mut inner_messages) = symbol_type.destructure();
                messages.append(&mut inner_messages);
                if let Some(symbol_type) = symbol_type {
                    let definition = DefinitionI {
                        name: definition.name.clone(),
                        type_variables: definition
                            .type_parameters
                            .iter()
                            .map(|param| TypeParameter {
                                name: param.name.name.clone(),
                                parameters: param.parameters,
                            })
                            .collect(),
                        symbol_type,
                    };
                    vacant.insert(definition);
                }
            }
        }
    }

    for data in &file_parsed.data {
        match types.entry(data.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    data.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add the definition into the map.
                let type_params = data
                    .type_params
                    .iter()
                    .map(|ident| ident.name.name.clone())
                    .collect::<HashSet<_>>();

                let type_ctor = data
                    .type_ctor
                    .fields
                    .iter()
                    .map(|field| {
                        let ty = crate::type_resolve::resolve_typep(
                            source_file,
                            &field.ty,
                            &type_params,
                            project_types,
                        );
                        ty.map(|ty| (field.name.clone(), ty))
                    })
                    .collect::<DiagnosticResult<Vec<_>>>()
                    .map(|fields| TypeConstructorI { fields });
                let (_, mut inner_messages) = type_ctor
                    .map(|type_ctor| {
                        let datai = DataI {
                            range: data.identifier.range,
                            type_params: data
                                .type_params
                                .iter()
                                .map(|param| TypeParameter {
                                    name: param.name.name.clone(),
                                    parameters: param.parameters,
                                })
                                .collect(),
                            type_ctor,
                        };
                        vacant.insert(TypeDeclarationI {
                            name: data.identifier.clone(),
                            decl_type: TypeDeclarationTypeI::Data(datai),
                        });
                    })
                    .destructure();
                messages.append(&mut inner_messages);
            }
        }
    }

    for an_enum in &file_parsed.enums {
        match types.entry(an_enum.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    an_enum.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add the definition into the map.
                let type_params = an_enum
                    .type_params
                    .iter()
                    .map(|ident| ident.name.name.clone())
                    .collect::<HashSet<_>>();

                let variants = an_enum
                    .alternatives
                    .iter()
                    .map(|variant| {
                        variant
                            .type_ctor
                            .fields
                            .iter()
                            .map(|field| {
                                let ty = crate::type_resolve::resolve_typep(
                                    source_file,
                                    &field.ty,
                                    &type_params,
                                    project_types,
                                );
                                ty.map(|ty| (field.name.clone(), ty))
                            })
                            .collect::<DiagnosticResult<Vec<_>>>()
                            .map(|fields| EnumVariant {
                                name: variant.name.clone(),
                                type_ctor: TypeConstructorI { fields },
                            })
                    })
                    .collect::<DiagnosticResult<Vec<_>>>();

                let (_, mut inner_messages) = variants
                    .bind(|variants| {
                        let mut messages = Vec::new();

                        for variant in &variants {
                            match enum_variant_types.entry(variant.name.name.clone()) {
                                Entry::Occupied(occupied) => messages.push(ErrorMessage::new(
                                    format!(
                                        "an enum variant called `{}` was already defined inside `{}`",
                                        variant.name.name,
                                        occupied.get(),
                                    ),
                                    Severity::Error,
                                    Diagnostic::at(source_file, &variant.name.range),
                                )),
                                Entry::Vacant(vacant) => {
                                    vacant.insert(an_enum.identifier.name.clone());
                                }
                            }
                        }

                        let enumi = EnumI {
                            range: an_enum.identifier.range,
                            type_params: an_enum
                                .type_params
                                .iter()
                                .map(|param| TypeParameter {
                                    name: param.name.name.clone(),
                                    parameters: param.parameters,
                                })
                                .collect(),
                            variants,
                        };

                        vacant.insert(TypeDeclarationI {
                            name: an_enum.identifier.clone(),
                            decl_type: TypeDeclarationTypeI::Enum(enumi),
                        });

                        DiagnosticResult::ok_with_many((), messages)
                    })
                    .destructure();

                messages.append(&mut inner_messages);
            }
        }
    }

    let index = FileIndex {
        types,
        definitions,
        enum_variant_types,
    };
    DiagnosticResult::ok_with_many(index, messages)
}
