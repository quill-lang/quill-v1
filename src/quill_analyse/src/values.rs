//! Perform basic static analysis on the MIR to deduce what value
//! each local variable holds, if knowable at compile time.
//! This will add special-case functions where impl parameters are known at compile time.

use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet, VecDeque},
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
    // eprintln!("deps: {:#?}", function_dependencies);

    // Run static analysis on each definition.
    let mut analysis_queue = function_dependencies
        .keys()
        .cloned()
        .collect::<VecDeque<_>>();

    let mut known_return_values = BTreeMap::new();

    while let Some(desc) = analysis_queue.pop_front() {
        let def = mir
            .files
            .get_mut(&desc.name.source_file)
            .unwrap()
            .definitions
            .get_mut(&desc.name.name)
            .unwrap()
            .get_mut(&desc.params)
            .unwrap();

        let result = analyse_values_def(def, &known_return_values);
        if let Some(return_value) = result.return_value {
            // The return value might have changed.
            let return_value_changed = match known_return_values.entry(desc.clone()) {
                Entry::Vacant(vacant) => {
                    vacant.insert(return_value);
                    true
                }
                Entry::Occupied(mut occupied) => {
                    if *occupied.get() == return_value {
                        false
                    } else {
                        occupied.insert(return_value);
                        true
                    }
                }
            };

            if return_value_changed {
                // The return value actually changed.
                // Re-analyse definitions that depend on this one.
                // FIXME: This could enter an infinite loop for (mutually) recursive functions.
                // TODO: This might add a function into the analysis queue multiple times -
                // this could be a problem making the queue very large.
                // We should optimise this once the time taken to compute this step becomes large.
                analysis_queue.extend(function_dependencies[&desc].iter().cloned());
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

struct AnalysisResult {
    return_value: Option<KnownValue>,
}

/// Work out what value each variable holds, if known at compile time.
fn analyse_values_def(
    def: &mut DefinitionM,
    known_return_values: &BTreeMap<FunctionDescriptor, KnownValue>,
) -> AnalysisResult {
    // Run through the control flow graph and work out what value each variable might hold.
    let cfg = match &mut def.body {
        DefinitionBodyM::PatternMatch(cfg) => cfg,
        DefinitionBodyM::CompilerIntrinsic => return AnalysisResult { return_value: None },
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
                    panic!("func objects has not been run yet")
                }
                StatementKind::InvokeFunction {
                    name,
                    type_variables,
                    target,
                    arguments,
                } => {
                    if !arguments.is_empty() {
                        panic!("arguments not supported");
                    }

                    // TODO: Extract this into an external function to unify with the ConstructFunctionObject block`
                    // Check if the value of the function is known.
                    let known_value = known_return_values.get(&FunctionDescriptor {
                        name: name.clone(),
                        params: MonomorphisationParameters {
                            type_parameters: type_variables.clone(),
                        },
                    });

                    let value = if let Some(known_value) = known_value {
                        known_value.clone()
                    } else {
                        KnownValue::Instantiate {
                            name: name.clone(),
                            type_variables: type_variables.clone(),
                            special_case_arguments: Vec::new(),
                        }
                    };

                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(value);
                }
                StatementKind::ConstructFunctionObject {
                    name,
                    type_variables,
                    target,
                    curried_arguments,
                    ..
                } => {
                    if !curried_arguments.is_empty() {
                        panic!("arguments not supported");
                    }

                    // Check if the value of the function is known.
                    let known_value = known_return_values.get(&FunctionDescriptor {
                        name: name.clone(),
                        params: MonomorphisationParameters {
                            type_parameters: type_variables.clone(),
                        },
                    });

                    let value = if let Some(known_value) = known_value {
                        known_value.clone()
                    } else {
                        KnownValue::Instantiate {
                            name: name.clone(),
                            type_variables: type_variables.clone(),
                            special_case_arguments: Vec::new(),
                        }
                    };

                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(value);
                }
                StatementKind::InvokeFunctionObject {
                    func_object,
                    target,
                    additional_arguments,
                } => {
                    // In the general case, we can't compute the result of a function call statically.
                    // However, if the argument is an impl, and the function is known, we can make a special case function
                    // for this specific case.
                    let (name, type_variables, mut special_case_arguments) =
                        if let Some(KnownValue::Instantiate {
                            name,
                            type_variables,
                            special_case_arguments,
                        }) = get_value_of_rvalue(&def.local_variable_names, func_object)
                        {
                            (name, type_variables, special_case_arguments)
                        } else {
                            continue 'stmt_loop;
                        };

                    for argument in additional_arguments {
                        // For each argument, check if it's an impl.
                        // If all arguments are impls, their values are stored in the list of special case arguments.
                        if let Some(the_impl @ KnownValue::ConstructImpl { .. }) =
                            get_value_of_rvalue(&def.local_variable_names, argument)
                        {
                            // We can make a special case function where the impl is known.
                            special_case_arguments.push(the_impl);
                        } else {
                            continue 'stmt_loop;
                        }
                    }

                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(KnownValue::Instantiate {
                        name,
                        type_variables,
                        special_case_arguments,
                    });
                }
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
    let return_value = if possible_return_values.len() == 1 {
        possible_return_values.pop().unwrap()
    } else {
        None
    };

    AnalysisResult { return_value }
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
