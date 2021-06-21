mod main_index;
mod type_index;
pub(crate) mod type_resolve;
use std::collections::HashMap;

pub use main_index::*;

use quill_common::{diagnostic::DiagnosticResult, location::SourceFileIdentifier};
use quill_parser::file::FileP;
use type_index::{compute_types_aspects, ProjectTypesAspectsC};

pub fn index_single_file(
    file_ident: &SourceFileIdentifier,
    parsed: &FileP,
) -> DiagnosticResult<FileIndex> {
    compute_types_aspects(file_ident, parsed)
        .bind(|cache| {
            let mut project_types = ProjectTypesAspectsC::new();
            project_types.insert(file_ident.clone(), cache);
            index(file_ident, parsed, &project_types)
        })
        .deny()
}

pub fn index_project(
    files: &HashMap<SourceFileIdentifier, FileP>,
) -> DiagnosticResult<ProjectIndex> {
    let project_types_cache =
        DiagnosticResult::sequence_unfail(files.iter().map(|(file, parsed)| {
            compute_types_aspects(file, parsed).map(|types| (file.clone(), types))
        }))
        .map(|file_types| file_types.into_iter().collect::<ProjectTypesAspectsC>())
        .deny();

    project_types_cache
        .bind(|project_types_cache| {
            DiagnosticResult::sequence_unfail(files.iter().map(|(file, parsed)| {
                index(file, parsed, &project_types_cache).map(|index| (file.clone(), index))
            }))
            .map(|index| index.into_iter().collect())
        })
        .deny()
}
