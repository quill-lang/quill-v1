//! The type index is an intermediate index that is executed first.
//! This allows the main index to guarantee that all types are known before indexing data structures which may contain these types.

use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
};

use either::Either;
use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::SourceFileIdentifier,
};
use quill_parser::{file::FileP, identifier::NameP};

/// A set of all types and aspects declared in a single module, mapping type names to their declarations.
pub type ModuleTypesAspectsC = HashMap<String, TypeDeclarationOrAspectC>;

/// All types and aspects known about in an entire project.
pub type ProjectTypesAspectsC = HashMap<SourceFileIdentifier, ModuleTypesAspectsC>;

#[derive(Debug)]
pub struct TypeDeclarationOrAspectC {
    pub name: NameP,
    pub ty: Either<TypeDeclarationC, AspectC>,
}

/// A type declaration, e.g. `data Foo ...` or `enum Option[T] ...`.
#[derive(Debug)]
pub struct TypeDeclarationC {
    pub decl_type: TypeDeclarationTypeC,
}

#[derive(Debug)]
pub enum TypeDeclarationTypeC {
    Data,
    Enum,
}

/// An aspect, such as `aspect Something { ... }`
/// For now, we don't track the definitions inside of the aspect.
#[derive(Debug)]
pub struct AspectC {}

/// Computes the types declared in the file.
pub(crate) fn compute_types_aspects(
    source_file: &SourceFileIdentifier,
    file_parsed: &FileP,
) -> DiagnosticResult<ModuleTypesAspectsC> {
    let mut messages = Vec::new();
    let mut types = ModuleTypesAspectsC::new();

    for data in &file_parsed.data {
        let entry = types.entry(data.identifier.name.clone());
        match entry {
            Entry::Occupied(occupied) => {
                // This type has already been defined.
                // This is an error.
                messages.push(ErrorMessage::new_with(
                    String::from("item with this name was already defined"),
                    Severity::Error,
                    Diagnostic::at(source_file, &data.identifier.range),
                    HelpMessage {
                        message: String::from("previously defined here"),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(source_file, &occupied.get().name.range),
                    },
                ));
            }
            Entry::Vacant(vacant) => {
                // This type has not yet been defined.
                // So, let's add it to the list of types.
                vacant.insert(TypeDeclarationOrAspectC {
                    name: data.identifier.clone(),
                    ty: Either::Left(TypeDeclarationC {
                        decl_type: TypeDeclarationTypeC::Data,
                    }),
                });
            }
        }
    }
    for an_enum in &file_parsed.enums {
        let entry = types.entry(an_enum.identifier.name.clone());
        match entry {
            Entry::Occupied(occupied) => {
                // This type has already been defined.
                // This is an error.
                messages.push(ErrorMessage::new_with(
                    String::from("item with this name was already defined"),
                    Severity::Error,
                    Diagnostic::at(source_file, &an_enum.identifier.range),
                    HelpMessage {
                        message: String::from("previously defined here"),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(source_file, &occupied.get().name.range),
                    },
                ));
            }
            Entry::Vacant(vacant) => {
                // This type has not yet been defined.
                // So, let's add it to the list of types.
                vacant.insert(TypeDeclarationOrAspectC {
                    name: an_enum.identifier.clone(),
                    ty: Either::Left(TypeDeclarationC {
                        decl_type: TypeDeclarationTypeC::Enum,
                    }),
                });
            }
        }
    }

    for aspect in &file_parsed.aspects {
        let entry = types.entry(aspect.identifier.name.clone());
        match entry {
            Entry::Occupied(occupied) => {
                // This type has already been defined.
                // This is an error.
                messages.push(ErrorMessage::new_with(
                    String::from("item with this name was already defined"),
                    Severity::Error,
                    Diagnostic::at(source_file, &aspect.identifier.range),
                    HelpMessage {
                        message: String::from("previously defined here"),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(source_file, &occupied.get().name.range),
                    },
                ));
            }
            Entry::Vacant(vacant) => {
                // This type has not yet been defined.
                // So, let's add it to the list of types.
                vacant.insert(TypeDeclarationOrAspectC {
                    name: aspect.identifier.clone(),
                    ty: Either::Right(AspectC {}),
                });
            }
        }
    }

    DiagnosticResult::ok_with_many(types, messages)
}
