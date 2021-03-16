use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage},
    location::SourceFileIdentifier,
};
use quill_mir::{DefinitionM, SourceFileMIR};
use quill_parser::NameP;
use quill_type_deduce::type_check::{Definition, Pattern, SourceFileHIR};

#[derive(Debug)]
enum BorrowStatus {
    Owned,
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
            borrow_check_definition(source_file_identifier, def).map(|checked| (def_name, checked))
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
    unimplemented!()
}
