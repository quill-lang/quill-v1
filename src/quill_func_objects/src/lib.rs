use std::collections::{BTreeMap, BTreeSet};

use quill_common::{location::Location, name::QualifiedName};
use quill_mir::mir::{DefinitionBodyM, DefinitionM, Statement, StatementKind};
use quill_monomorphise::{
    mono_mir::MonomorphisedMIR,
    monomorphisation::{CurryStatus, MonomorphisationParameters},
};

/// Converts curried functions and partial application of functions into more LLVM-friendly representations.
pub fn convert_func_objects(project: &mut MonomorphisedMIR) {
    // First, cache the arities of each function.
    // We need to know exactly how many arguments a function "really" has, and how many are coalesced into the result type of the function.
    let mut arities = BTreeMap::new();
    for (fname, file) in &project.files {
        for (def_name, defs) in &file.definitions {
            arities.insert(
                QualifiedName {
                    source_file: fname.clone(),
                    name: def_name.clone(),
                    range: Location { line: 0, col: 0 }.into(),
                },
                defs.iter()
                    .map(|(params, def)| (params.clone(), def.def.arity))
                    .collect::<BTreeMap<_, _>>(),
            );
        }
    }

    let mut curry_steps_used = BTreeMap::new();

    for file in project.files.values_mut() {
        for defs in file.definitions.values_mut() {
            for def in defs.values_mut() {
                convert_def(&mut def.def, &arities, &mut curry_steps_used);
            }
        }
    }

    // Update the MIR with the known set of curry steps.
    for (name, map) in curry_steps_used {
        let defs = project
            .files
            .get_mut(&name.source_file)
            .unwrap()
            .definitions
            .get_mut(&name.name)
            .unwrap();
        for (params, curry_statuses) in map {
            defs.get_mut(&params).unwrap().curry_possibilities = curry_statuses;
        }
    }
    project
        .files
        .get_mut(&project.entry_point.source_file)
        .unwrap()
        .definitions
        .get_mut(&project.entry_point.name)
        .unwrap()
        .get_mut(&MonomorphisationParameters::new(Vec::new()))
        .unwrap()
        .curry_possibilities = {
        let mut set = BTreeSet::new();
        set.insert(CurryStatus {
            curry_steps: Vec::new(),
            direct: true,
        });
        set
    };
}

fn convert_def(
    def: &mut DefinitionM,
    arities: &BTreeMap<QualifiedName, BTreeMap<MonomorphisationParameters, u64>>,
    curry_steps_used: &mut BTreeMap<
        QualifiedName,
        BTreeMap<MonomorphisationParameters, BTreeSet<CurryStatus>>,
    >,
) {
    if let DefinitionBodyM::PatternMatch(cfg) = &mut def.body {
        for block in cfg.basic_blocks.values_mut() {
            block.statements = block
                .statements
                .drain(..)
                .map(|stmt| convert_stmt(stmt, arities, curry_steps_used))
                .flatten()
                .collect();
        }
    }
}

/// Converts functional statements (InstanceSymbol, Apply) to imperative statements (ConstructFunctionObject, InvokeFunction, etc.)
/// In this step, all function objects are considered to be unary. A later optimisation step will construct n-ary functions.
fn convert_stmt(
    stmt: Statement,
    arities: &BTreeMap<QualifiedName, BTreeMap<MonomorphisationParameters, u64>>,
    curry_steps_used: &mut BTreeMap<
        QualifiedName,
        BTreeMap<MonomorphisationParameters, BTreeSet<CurryStatus>>,
    >,
) -> Vec<Statement> {
    match stmt.kind {
        StatementKind::InstanceSymbol {
            name,
            type_variables,
            special_case_arguments,
            target,
        } => {
            let arity = *arities
                .get(&name)
                .expect("function did not exist")
                .get(
                    &MonomorphisationParameters::new(type_variables.clone())
                        .with_args(special_case_arguments.iter().cloned()),
                )
                .expect("function had incorrect monomorphisation parameters");
            // Store the fact that the target is a function object.
            // new_infos.insert(target, v)

            if arity == 0 {
                // If the function is a nullary function, i.e. a (possibly polymorphic) constant, a function with no arguments,
                // then we can call it right away.
                curry_steps_used
                    .entry(name.clone())
                    .or_default()
                    .entry(
                        MonomorphisationParameters::new(type_variables.clone())
                            .with_args(special_case_arguments.iter().cloned()),
                    )
                    .or_default()
                    .insert(CurryStatus {
                        curry_steps: Vec::new(),
                        direct: true,
                    });
                vec![Statement {
                    range: stmt.range,
                    kind: StatementKind::InvokeFunction {
                        name,
                        type_variables,
                        special_case_arguments,
                        target,
                        arguments: Vec::new(),
                    },
                }]
            } else {
                // We need to create a new "dummy" function that applies one argument to this function.
                let entry = curry_steps_used
                    .entry(name.clone())
                    .or_default()
                    .entry(
                        MonomorphisationParameters::new(type_variables.clone())
                            .with_args(special_case_arguments.iter().cloned()),
                    )
                    .or_default();
                entry.insert(CurryStatus {
                    curry_steps: std::iter::repeat(1).take(arity as usize).collect(),
                    direct: true,
                });
                for i in 1..=arity {
                    entry.insert(CurryStatus {
                        curry_steps: std::iter::repeat(1).take(i as usize).collect(),
                        direct: false,
                    });
                }

                vec![Statement {
                    range: stmt.range,
                    kind: StatementKind::ConstructFunctionObject {
                        name,
                        type_variables,
                        special_case_arguments,
                        target,
                        curry_steps: std::iter::repeat(1).take(arity as usize).collect(),
                        curried_arguments: Vec::new(),
                    },
                }]
            }
        }
        StatementKind::Apply {
            argument,
            function,
            target,
        } => {
            // In this step, the function is always going to be a function object.
            // We should now execute it with the InvokeFunctionObject instruction, because at this point of compilation,
            // all function objects are unary.
            // This instruction may return another function object.
            vec![Statement {
                range: stmt.range,
                kind: StatementKind::InvokeFunctionObject {
                    func_object: *function,
                    target,
                    additional_arguments: vec![*argument],
                },
            }]
        }
        kind => vec![Statement {
            range: stmt.range,
            kind,
        }],
    }
}
