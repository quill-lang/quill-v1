//! This module contains the mid-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

mod definition;
mod expr;
mod impls;
pub mod mir;
mod pattern_match;
mod validate;

use std::{collections::BTreeMap, fmt::Display};

use mir::{
    ArgumentIndex, ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableId,
    LocalVariableInfo, LocalVariableName,
};
use quill_common::{
    diagnostic::DiagnosticResult, location::SourceFileIdentifier, name::QualifiedName,
};
use quill_index::{DefinitionI, ProjectIndex, TypeParameter};
use quill_type::Type;
use quill_type_deduce::hir::SourceFileHIR;

use crate::mir::{BasicBlock, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind};

#[derive(Debug)]
pub struct ProjectMIR {
    pub files: BTreeMap<SourceFileIdentifier, SourceFileMIR>,
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
    pub definitions: BTreeMap<String, mir::DefinitionM>,
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
) -> DiagnosticResult<SourceFileMIR> {
    let definitions =
        file.definitions
            .into_iter()
            .map(|(def_name, def)| {
                definition::to_mir_def(project_index, def, source_file, def_name.as_str(), &mut 0)
                    .map(|(def, inner_defs)| {
                        std::iter::once((def_name.clone(), def)).chain(
                            inner_defs
                                .into_iter()
                                .enumerate()
                                .map(move |(i, def)| (format!("{}/lambda/{}", &def_name, i), def)),
                        )
                    })
            })
            .collect::<DiagnosticResult<Vec<_>>>();

    // Create definitions for implicitly generated functions,
    // i.e. definitions defined inside impls.
    let definitions = definitions.map(|definitions| {
        let new_definitions = project_index
            .get_file_index(source_file)
            .aspects
            .iter()
            .map(|(aspect_name, aspecti)| {
                let aspect_type_vars = aspecti.type_variables.to_vec();
                aspecti.definitions.iter().map(move |def| {
                    create_aspect_def_mir(def, source_file, aspect_name, &aspect_type_vars)
                })
            })
            .flatten();

        definitions
            .into_iter()
            .flatten()
            .chain(new_definitions)
            .collect::<BTreeMap<_, _>>()
    });

    definitions.deny().map(|definitions| {
        let result = SourceFileMIR { definitions };
        // Uncomment this if the `validate` function itself panics.
        // eprintln!("{}", result);
        if let Err(err) = validate::validate(project_index, source_file, &result) {
            panic!(
                "mir failed to validate in def {} at {} {}: {}\n{}",
                err.def_name,
                err.block_id,
                if let Some(stmt) = err.statement_id {
                    format!("st{}", stmt)
                } else {
                    "term".to_string()
                },
                err.message,
                result
            );
        }
        result
    })
}

fn create_aspect_def_mir(
    def: &DefinitionI,
    source_file: &SourceFileIdentifier,
    aspect_name: &str,
    aspect_type_vars: &[TypeParameter],
) -> (String, DefinitionM) {
    let range = def.name.range;

    // Create the MIR for the auto-generated function.
    // If `def` has type `T`, then we generate a function of type `impl -> T`.
    let mut local_variable_names = BTreeMap::new();
    let mut the_cfg = ControlFlowGraph::new();
    // Create the argument.
    local_variable_names.insert(
        LocalVariableName::Argument(ArgumentIndex(0)),
        LocalVariableInfo {
            range,
            ty: Type::Impl {
                name: QualifiedName {
                    source_file: source_file.clone(),
                    name: aspect_name.to_string(),
                    range,
                },
                parameters: aspect_type_vars
                    .iter()
                    .map(|param| Type::Variable {
                        variable: param.name.clone(),
                        parameters: Vec::new(),
                    })
                    .collect(),
            },
            name: Some("the impl".to_string()),
        },
    );

    // Extract the relevant function from the impl.
    local_variable_names.insert(
        LocalVariableName::Local(LocalVariableId(0)),
        LocalVariableInfo {
            range,
            ty: def.symbol_type.clone(),
            name: Some("return value".to_string()),
        },
    );
    let statement = Statement {
        range,
        kind: StatementKind::Assign {
            target: LocalVariableName::Local(LocalVariableId(0)),
            source: Rvalue::Move(
                Place::new(LocalVariableName::Argument(ArgumentIndex(0))).then(
                    mir::PlaceSegment::ImplField {
                        field: def.name.name.clone(),
                    },
                ),
            ),
        },
    };
    let terminator = Terminator {
        range,
        kind: TerminatorKind::Return {
            value: LocalVariableName::Local(LocalVariableId(0)),
        },
    };

    the_cfg.new_basic_block(BasicBlock {
        statements: vec![statement],
        terminator,
    });

    (
        def.name.name.clone(),
        DefinitionM {
            range,
            type_variables: aspect_type_vars
                .iter()
                .chain(&def.type_variables)
                .cloned()
                .collect(),
            arity: 1,
            local_variable_names,
            return_type: def.symbol_type.clone(),
            body: DefinitionBodyM::PatternMatch(the_cfg),
        },
    )
}
