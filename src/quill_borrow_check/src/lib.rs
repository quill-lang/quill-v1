mod ownership;

use quill_common::{
    diagnostic::{DiagnosticResult, ErrorMessage},
    location::SourceFileIdentifier,
};
use quill_mir::{mir::DefinitionM, SourceFileMIR};

/// Checks to make sure that borrows of data do not outlive the data they borrow,
/// and to make sure that once data is not used when it is not owned.
/// This mostly implements the algorithm described [here](https://rust-lang.github.io/rfcs/2094-nll.html),
/// notably excluding mutable references, since Quill does not have a notion of mutable references.
pub fn borrow_check(
    source_file: &SourceFileIdentifier,
    mut mir: SourceFileMIR,
) -> DiagnosticResult<SourceFileMIR> {
    let mut messages = Vec::new();
    for (_def_name, def) in mir.definitions.iter_mut() {
        // println!("dn {}", _def_name);
        borrow_check_def(source_file, def, &mut messages);
    }
    DiagnosticResult::ok_with_many(mir, messages)
}

/// Walk through the control flow graph, generating and solving lifetime constraints.
fn borrow_check_def(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
) {
    // First, check to see if data ownership is valid.
    // Then, we'll check to see if lifetimes are valid.
    // Currently, lifetimes and borrowing are not features of the language, so we'll just do data ownership for now.

    ownership::check_ownership(source_file, def, messages);
}
