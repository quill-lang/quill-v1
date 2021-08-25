//! Perform basic static analysis on the MIR to deduce what value
//! each local variable holds, if knowable at compile time.

use std::collections::BTreeMap;

use crate::mir::{
    DefinitionBodyM, DefinitionM, KnownValue, LocalVariableInfo, LocalVariableName, Place, Rvalue,
    StatementKind, TerminatorKind,
};

/// Work out what value each variable holds, if known at compile time.
pub fn analyse_values(def: &mut DefinitionM) {
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