//! This module contains the mid-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

mod definition;
mod expr;
pub mod mir;
mod pattern_match;

use std::{collections::HashMap, fmt::Display};

use quill_common::{location::SourceFileIdentifier, name::QualifiedName};
use quill_index::ProjectIndex;
use quill_type_deduce::hir::SourceFileHIR;

#[derive(Debug)]
pub struct ProjectMIR {
    pub files: HashMap<SourceFileIdentifier, SourceFileMIR>,
    /// The qualified name where the "main" function is.
    pub entry_point: QualifiedName,
    pub index: ProjectIndex,
}

impl Display for ProjectMIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "entry point {}", self.entry_point)?;
        for (id, mir) in &self.files {
            writeln!(f, "\n=====\n{}\n{}", id, mir)?;
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, mir::DefinitionM>,
}

impl Display for SourceFileMIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (id, def) in &self.definitions {
            writeln!(f, "\n---\n{}\n{}", id, def)?;
        }
        Ok(())
    }
}

/// Converts all expressions into control flow graphs.
pub fn to_mir(
    project_index: &ProjectIndex,
    file: SourceFileHIR,
    source_file: &SourceFileIdentifier,
) -> SourceFileMIR {
    let definitions = file
        .definitions
        .into_iter()
        .map(|(def_name, def)| {
            let (def, inner_defs) =
                definition::to_mir_def(project_index, def, source_file, def_name.as_str(), &mut 0);
            std::iter::once((def_name.clone(), def)).chain(
                inner_defs
                    .into_iter()
                    .enumerate()
                    .map(move |(i, def)| (format!("{}/lambda/{}", &def_name, i), def)),
            )
        })
        .flatten()
        .collect();

    SourceFileMIR { definitions }
}
