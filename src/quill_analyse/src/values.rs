//! Perform basic static analysis on the MIR to deduce what value
//! each local variable holds, if knowable at compile time.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Debug,
};

use quill_common::{location::Location, name::QualifiedName};
use quill_mir::mir::{
    DefinitionBodyM, DefinitionM, KnownValue, LocalVariableInfo, LocalVariableName, Place, Rvalue,
    StatementKind, TerminatorKind,
};
use quill_monomorphise::{
    mono_mir::MonomorphisedMIR, monomorphisation::MonomorphisationParameters,
};

pub fn analyse_values(mir: &mut MonomorphisedMIR) {
    // Work out which functions depend on which other functions.
    let function_dependencies = analyse_function_dependencies(mir);
    eprintln!("deps: {:#?}", function_dependencies);

    // Run static analysis on each definition.
    for file in mir.files.values_mut() {
        for defs in file.definitions.values_mut() {
            for def in defs.values_mut() {
                analyse_values_def(def);
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct FunctionDescriptor {
    name: QualifiedName,
    params: MonomorphisationParameters,
}

impl Debug for FunctionDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.name, self.params)
    }
}

/// If a function A calls another function B,
/// then the return value contains a mapping B -> A.
/// This means that when info about B is deduced, we can find all A that depend on this new info.
fn analyse_function_dependencies(
    mir: &MonomorphisedMIR,
) -> BTreeMap<FunctionDescriptor, BTreeSet<FunctionDescriptor>> {
    let mut result = BTreeMap::<FunctionDescriptor, BTreeSet<FunctionDescriptor>>::new();
    for (file_name, file) in &mir.files {
        for (def_name, defs) in &file.definitions {
            for (def_mono, def) in defs {
                if let DefinitionBodyM::PatternMatch(cfg) = &def.body {
                    for block in cfg.basic_blocks.values() {
                        for stmt in &block.statements {
                            match &stmt.kind {
                                StatementKind::InvokeFunction {
                                    name,
                                    type_variables,
                                    ..
                                }
                                | StatementKind::ConstructFunctionObject {
                                    name,
                                    type_variables,
                                    ..
                                } => {
                                    result
                                        .entry(FunctionDescriptor {
                                            name: name.clone(),
                                            params: MonomorphisationParameters {
                                                type_parameters: type_variables.clone(),
                                            },
                                        })
                                        .or_default()
                                        .insert(FunctionDescriptor {
                                            name: QualifiedName {
                                                source_file: file_name.clone(),
                                                name: def_name.clone(),
                                                range: Location { line: 0, col: 0 }.into(),
                                            },
                                            params: def_mono.clone(),
                                        });
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
    }
    result
}

/// Work out what value each variable holds, if known at compile time.
pub fn analyse_values_def(def: &mut DefinitionM) {
    // Run through the control flow graph and work out what value each variable might hold.
    let cfg = match &mut def.body {
        DefinitionBodyM::PatternMatch(cfg) => cfg,
        DefinitionBodyM::CompilerIntrinsic => return,
    };

    let mut possible_return_values = Vec::new();

    for block in cfg.basic_blocks.values() {
        'stmt_loop: for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign { target, source } => {
                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = get_value_of_rvalue(&def.local_variable_names, source);
                }
                StatementKind::AssignPhi { .. } => {
                    // We can't know the result of an assign phi node statically,
                    // unless there was really only one case.
                    // TODO: detect if there was only one case
                }
                StatementKind::InstanceSymbol { .. } => {
                    // This is removed by the func_objects pass.
                    // This analysis step happens after func_objects.
                    panic!("func objects has not been run yet");
                }
                StatementKind::Apply { .. } => {
                    // In the general case, we can't compute the result of a function call statically.
                    // TODO: make an effort to find the result somehow if the function call is a default impl or something?
                }
                StatementKind::InvokeFunction {
                    name,
                    type_variables,
                    target,
                    arguments,
                } => {
                    if arguments.is_empty() {
                        def.local_variable_names
                            .get_mut(target)
                            .unwrap()
                            .details
                            .value = Some(KnownValue::Instantiate {
                            name: name.clone(),
                            type_variables: type_variables.clone(),
                        });
                    }
                }
                StatementKind::ConstructFunctionObject {
                    name,
                    type_variables,
                    target,
                    curried_arguments,
                    ..
                } => {
                    if curried_arguments.is_empty() {
                        def.local_variable_names
                            .get_mut(target)
                            .unwrap()
                            .details
                            .value = Some(KnownValue::Instantiate {
                            name: name.clone(),
                            type_variables: type_variables.clone(),
                        });
                    }
                }
                StatementKind::InvokeFunctionObject { .. } => {}
                StatementKind::Drop { .. } => {}
                StatementKind::Free { .. } => {}
                StatementKind::ConstructData {
                    name,
                    type_variables,
                    variant,
                    fields,
                    target,
                } => {
                    let mut field_values = BTreeMap::new();
                    for (field_name, field_rvalue) in fields {
                        if let Some(field_value) =
                            get_value_of_rvalue(&def.local_variable_names, field_rvalue)
                        {
                            field_values.insert(field_name.clone(), field_value);
                        } else {
                            continue 'stmt_loop;
                        }
                    }
                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(KnownValue::ConstructData {
                        name: name.clone(),
                        type_variables: type_variables.clone(),
                        variant: variant.clone(),
                        fields: field_values,
                    });
                }
                StatementKind::ConstructImpl {
                    aspect,
                    type_variables,
                    definitions,
                    target,
                } => {
                    let mut definition_values = BTreeMap::new();
                    for (definition_name, definition_value) in definitions {
                        if let Some(definition_value) = def.local_variable_names[definition_value]
                            .details
                            .value
                            .as_ref()
                        {
                            definition_values
                                .insert(definition_name.clone(), definition_value.clone());
                        } else {
                            continue 'stmt_loop;
                        }
                    }
                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(KnownValue::ConstructImpl {
                        aspect: aspect.clone(),
                        type_variables: type_variables.clone(),
                        definitions: definition_values,
                    });
                }
            }
        }

        if let TerminatorKind::Return { value } = &block.terminator.kind {
            possible_return_values.push(def.local_variable_names[value].details.value.clone());
        }
    }

    // If the return value is known, store it.
    if possible_return_values.len() == 1 {
        cfg.return_value = possible_return_values.pop().unwrap();
    }
}

/// Gets the value of this rvalue, if it is statically known.
fn get_value_of_rvalue(
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Option<KnownValue> {
    match rvalue {
        Rvalue::Move(place) => get_value_of_place(locals, place),
        // For now, we won't statically analyse values behind borrows and copies.
        Rvalue::Borrow(_) | Rvalue::Copy(_) => None,
        Rvalue::Constant(constant) => Some(KnownValue::Constant(*constant)),
    }
}

/// Gets the value of this place, if it is statically known.
fn get_value_of_place(
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    place: &Place,
) -> Option<KnownValue> {
    if place.projection.is_empty() {
        locals[&place.local].details.value.clone()
    } else {
        None
    }
}
