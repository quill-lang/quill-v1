use std::collections::HashMap;

use crate::mir::{DefinitionM, ExpressionM, SourceFileMIR};
use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage},
    location::SourceFileIdentifier,
};
use quill_parser::NameP;
use quill_type::Type;
use quill_type_deduce::type_check::{
    Definition, DefinitionCase, Expression, ExpressionContentsGeneric, Pattern, SourceFileHIR,
};

/// An object has been borrowed.
#[derive(Debug)]
struct Borrow {}

/// Tracks the borrow status of a single object inside a scope.
#[derive(Debug)]
enum BorrowStatus {
    /// The object, and everything it owns, is owned.
    Owned,
    /// The object has been moved out of this scope or otherwise destroyed or destructured,
    /// and we are now no longer allowed to access it, or anything it owns.
    Moved,
    /// The object has been borrowed, or a part of it has been borrowed/moved.
    PartialMove {
        borrows: Vec<Borrow>,
        /// If this is a data type, its fields may be borrowed independently of the main object,
        /// or moved out at any time (provided that the object itself does not have a destructor).
        fields: HashMap<NameP, BorrowStatus>,
    },
}

/// Checks the borrow and ownership status of each variable in every expression in a source file,
/// converting it into MIR.
pub fn borrow_check(
    source_file_identifier: &SourceFileIdentifier,
    source_file: SourceFileHIR,
) -> DiagnosticResult<SourceFileMIR> {
    let definitions = source_file
        .definitions
        .into_iter()
        .map(|(def_name, def)| {
            borrow_check_definition(source_file_identifier, def)
                .map(|checked| (def_name, checked))
        })
        .collect::<DiagnosticResult<Vec<_>>>();
    let definitions = definitions.map(|defs| {
        let mut map = HashMap::new();
        map.extend(defs);
        map
    });

    definitions.map(|definitions| SourceFileMIR { definitions })
}

/// Checks the borrow and ownership status of each variable in an expression,
/// converting it into MIR.
fn borrow_check_definition(
    source_file_identifier: &SourceFileIdentifier,
    definition: Definition,
) -> DiagnosticResult<DefinitionM> {
    // Cache the types and borrow statuses of all the named values in the argument patterns.
    if definition.cases.is_empty() {
        panic!("definition cases empty, bottom type not implemented yet");
    }

    for case in &definition.cases {
        let mut borrow_statuses = HashMap::new();
        for pat in &case.arg_patterns {
            borrow_statuses.extend(cache_arg_pattern(pat));
        }
        println!("Def: {:#?}", borrow_statuses);
    }
    DiagnosticResult::fail(ErrorMessage::new(
        "test".to_string(),
        quill_common::diagnostic::Severity::Error,
        Diagnostic::in_file(source_file_identifier),
    ))
}

/// Returns a map from names of variables to their borrow statuses.
fn cache_arg_pattern(
    pat: &Pattern,
) -> HashMap<NameP, BorrowStatus> {
    match pat {
        Pattern::Named(name) => {
            let mut map = HashMap::new();
            map.insert(name.clone(), BorrowStatus::Owned);
            map
        }
        Pattern::TypeConstructor { fields, .. } => {
            let mut map = HashMap::new();
            for (_field_name, pat) in fields {
                map.extend(cache_arg_pattern(pat));
            }
            map
        }
        Pattern::Function { .. } => {
            unreachable!("functions are forbidden in arg patterns")
        }
        Pattern::Unknown(_) => HashMap::new(),
    }
}
