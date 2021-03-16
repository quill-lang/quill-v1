//! The type index is an intermediate index that is executed first.
//! This allows the main index to guarantee that all types are known before indexing data structures which may contain these types.

use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::SourceFileIdentifier,
};
use quill_parser::{FileP, NameP};

/// A set of all types declared in a single module, mapping type names to their declarations.
pub type ModuleTypesC = HashMap<String, TypeDeclarationC>;

/// All types known about in an entire project.
pub type ProjectTypesC = HashMap<SourceFileIdentifier, ModuleTypesC>;

/// A type declaration, e.g. `data Foo ...` or `enum Option[T] ...`.
#[derive(Debug)]
pub struct TypeDeclarationC {
    pub name: NameP,
    pub decl_type: TypeDeclarationTypeC,
}

#[derive(Debug)]
pub enum TypeDeclarationTypeC {
    Data,
    Enum,
}

/// Computes the types declared in the file.
pub fn compute_types(
    source_file: &SourceFileIdentifier,
    file_parsed: &FileP,
) -> DiagnosticResult<ModuleTypesC> {
    let mut messages = Vec::new();
    let mut types = ModuleTypesC::new();
    for data in &file_parsed.data {
        let entry = types.entry(data.identifier.name.clone());
        match entry {
            Entry::Occupied(occupied) => {
                // This type has already been defined.
                // This is an error.
                messages.push(ErrorMessage::new_with(
                    String::from("type with this name was already defined"),
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
                vacant.insert(TypeDeclarationC {
                    name: data.identifier.clone(),
                    decl_type: TypeDeclarationTypeC::Data,
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
                    String::from("type with this name was already defined"),
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
                vacant.insert(TypeDeclarationC {
                    name: an_enum.identifier.clone(),
                    decl_type: TypeDeclarationTypeC::Enum,
                });
            }
        }
    }

    DiagnosticResult::ok_with_many(types, messages)
}
