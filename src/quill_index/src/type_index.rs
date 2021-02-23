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

/// A type declaration, e.g. `data Bool = True {} | False {}`.
#[derive(Debug)]
pub struct TypeDeclarationC {
    pub name: NameP,
    pub decl_type: TypeDeclarationTypeC,
}

#[derive(Debug)]
pub enum TypeDeclarationTypeC {
    Data(DataC),
}

/// A `data` statement, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct DataC {
    /// A list of all the type constructors for a `data` statement. For example, in `data Bool = True | False`, the two
    /// type constructors are `True` and `False`.
    pub type_ctors: Vec<TypeConstructorC>,
}

#[derive(Debug)]
pub struct TypeConstructorC {
    pub name: NameP,
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
                let mut type_ctors = Vec::<TypeConstructorC>::new();
                for type_ctor in &data.type_ctors {
                    // Is this a duplicate type constructor name?
                    let mut was_valid = true;
                    for validated_type_ctor in &type_ctors {
                        if type_ctor.name.name == validated_type_ctor.name.name {
                            was_valid = false;
                            messages.push(ErrorMessage::new_with(
                                String::from("type constructor with this name was already defined"),
                                Severity::Error,
                                Diagnostic::at(source_file, &type_ctor.name.range),
                                HelpMessage {
                                    message: String::from("previously defined here"),
                                    help_type: HelpType::Note,
                                    diagnostic: Diagnostic::at(
                                        source_file,
                                        &validated_type_ctor.name.range,
                                    ),
                                },
                            ))
                        }
                    }
                    if was_valid {
                        type_ctors.push(TypeConstructorC {
                            name: type_ctor.name.clone(),
                        });
                    }
                }
                vacant.insert(TypeDeclarationC {
                    name: data.identifier.clone(),
                    decl_type: TypeDeclarationTypeC::Data(DataC { type_ctors }),
                });
            }
        }
    }

    DiagnosticResult::ok_with_many(types, messages)
}
