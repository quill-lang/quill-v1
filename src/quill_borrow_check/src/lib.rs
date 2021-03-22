use std::collections::HashMap;

use quill_common::{
    diagnostic::{DiagnosticResult, ErrorMessage},
    location::Range,
};
use quill_mir::{DefinitionM, LocalVariableName, SourceFileMIR};

/// Checks to make sure that borrows of data do not outlive the data they borrow,
/// and to make sure that once data is not used when it is not owned.
/// This mostly implements the algorithm described [here](https://rust-lang.github.io/rfcs/2094-nll.html),
/// notably excluding mutable references, since Quill does not have a notion of mutable references.
pub fn borrow_check(mut mir: SourceFileMIR) -> DiagnosticResult<SourceFileMIR> {
    let mut messages = Vec::new();
    for (_def_name, def) in mir.definitions.iter_mut() {
        borrow_check_def(def, &mut messages);
    }
    DiagnosticResult::ok_with_many(mir, messages)
}

/// Walk through the control flow graph, generating and solving lifetime constraints.
fn borrow_check_def(def: &mut DefinitionM, messages: &mut Vec<ErrorMessage>) {
    // First, check to see if data ownership is valid.
    // Then, we'll check to see if lifetimes are valid.
    // Currently, lifetimes and borrowing are not features of the language, so we'll just do data ownership for now.

    check_ownership(def, messages);
}

enum OwnershipStatus {
    Owned,
    Moved,
    Dropped,
}

/// Checks whether data is owned when it is used or referenced.
/// We walk through all branches of the control flow graph deducing ownership (but not borrow) status.
/// This allows us to insert StorageLive, StorageDead, and Drop instructions into the MIR, assuming that all
/// values are dropped at the end of the scope where they are defined, unless they are moved out beforehand.
fn check_ownership(def: &mut DefinitionM, messages: &mut Vec<ErrorMessage>) {}
