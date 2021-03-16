mod main_index;
mod type_index;
pub(crate) mod type_resolve;
pub use main_index::*;

use quill_common::{diagnostic::DiagnosticResult, location::SourceFileIdentifier};
use quill_parser::FileP;
use type_index::{compute_types, ProjectTypesC};

pub fn index_single_file(
    file_ident: &SourceFileIdentifier,
    parsed: &FileP,
) -> DiagnosticResult<FileIndex> {
    // TODO move this `deny` to an outer level, such as a function to index an entire project.
    compute_types(&file_ident, &parsed)
        .bind(|cache| {
            let mut project_types = ProjectTypesC::new();
            project_types.insert(file_ident.clone(), cache);
            index(&file_ident, &parsed, &project_types)
        })
        .deny()
}
