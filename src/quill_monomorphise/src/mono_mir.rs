use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    fmt::Display,
};

use quill_common::{location::SourceFileIdentifier, name::QualifiedName};
use quill_index::ProjectIndex;
use quill_mir::{mir::DefinitionM, ProjectMIR};
use quill_type::Type;

use crate::{
    monomorphisation::{MonomorphisationParameters, MonomorphisedFunction},
    monomorphise::monomorphise,
};

/// The monomorphised MIR is the MIR for each monomorphised function.
/// This is the equivalent of ProjectMIR after monomorphisation.
#[derive(Debug)]
pub struct MonomorphisedMIR {
    pub files: BTreeMap<SourceFileIdentifier, MonomorphisedSourceFile>,
    /// The qualified name where the "main" function is.
    pub entry_point: QualifiedName,
    pub index: ProjectIndex,
}

impl Display for MonomorphisedMIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "entry point {}", self.entry_point)?;
        for (id, mir) in &self.files {
            writeln!(f, "\n=====\n{}\n{}", id, mir)?;
        }
        Ok(())
    }
}

#[derive(Debug, Default)]
pub struct MonomorphisedSourceFile {
    pub definitions: BTreeMap<String, BTreeMap<MonomorphisationParameters, DefinitionM>>,
}

impl Display for MonomorphisedSourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (id, defs) in &self.definitions {
            writeln!(f, "\n---\n{}", id)?;
            for (param, def) in defs {
                writeln!(f, "~~~\n{}\n{}\n", param, def)?;
            }
        }
        Ok(())
    }
}

impl MonomorphisedMIR {
    /// Construct a monomorphisation of a project's MIR.
    /// TODO: maybe remove has_repr and make the LIR backend (#132) delete instructions with reprs?
    pub fn new(
        mir: ProjectMIR,
        mono_functions: &BTreeSet<MonomorphisedFunction>,
        has_repr: impl Fn(Type) -> bool,
    ) -> Self {
        let mut files = BTreeMap::<SourceFileIdentifier, MonomorphisedSourceFile>::new();
        for func in mono_functions {
            if let Entry::Vacant(entry) = files
                .entry(func.func.source_file.clone())
                .or_default()
                .definitions
                .entry(func.func.name.clone())
                .or_default()
                .entry(func.mono.clone())
            {
                let mono_func = monomorphise(
                    // Using a closure lets us avoid requiring Clone on has_repr.
                    |val| has_repr(val),
                    func,
                    &mir.files[&func.func.source_file].definitions[&func.func.name],
                );
                entry.insert(mono_func);
            }
        }
        Self {
            files,
            entry_point: mir.entry_point,
            index: mir.index,
        }
    }

    pub fn analyse(&mut self) {
        // Now, run static analysis on each definition.
        for file in self.files.values_mut() {
            for defs in file.definitions.values_mut() {
                for def in defs.values_mut() {
                    quill_analyse::analyse_values(def);
                }
            }
        }
    }
}
