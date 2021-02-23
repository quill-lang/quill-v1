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
}

/// A `data` statement, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct DataI {
    /// Where was this data statement written?
    pub range: Range,
    pub type_params: Vec<TypeParameter>,
    /// A list of all the type constructors for a `data` statement. For example, in `data Bool = True {} | False {}`, the two
    /// type constructors are `True` and `False`.
    pub type_ctors: Vec<TypeConstructorI>,
}

#[derive(Debug)]
pub struct TypeConstructorI {
    pub name: String,
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
    let mut symbols = HashMap::<String, DefinitionI>::new();

    for definition in &file_parsed.definitions {
        match symbols.entry(definition.name.name.clone()) {
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

                let type_ctors = data
                    .type_ctors
                    .iter()
                    .map(|type_ctor| {
                        type_ctor
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
                            .map(|fields| TypeConstructorI {
                                name: type_ctor.name.name.clone(),
                                fields,
                            })
                    })
                    .collect::<DiagnosticResult<Vec<_>>>();
                let (_, mut inner_messages) = type_ctors
                    .map(|type_ctors| {
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
                            type_ctors,
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

    let index = FileIndex {
        types,
        definitions: symbols,
    };
    DiagnosticResult::ok_with_many(index, messages)
}
