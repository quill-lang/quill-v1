//! Perform basic static analysis on the MIR to deduce what value
//! each local variable holds, if knowable at compile time.

use std::collections::BTreeMap;

use crate::mir::{
    DefinitionBodyM, DefinitionM, KnownValue, LocalVariableInfo, LocalVariableName, Place, Rvalue,
    StatementKind,
};

pub(crate) fn analyse(def: &mut DefinitionM) {
    // Run through the control flow graph and work out what value each variable might hold.
    let cfg = match &def.body {
        DefinitionBodyM::PatternMatch(cfg) => cfg,
        DefinitionBodyM::CompilerIntrinsic => return,
    };

    for block in cfg.basic_blocks.values() {
        for stmt in &block.statements {
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
                StatementKind::InstanceSymbol {
                    name,
                    type_variables,
                    target,
                } => {}
                StatementKind::Apply {
                    argument,
                    function,
                    target,
                } => {}
                StatementKind::InvokeFunction {
                    name,
                    type_variables,
                    target,
                    arguments,
                } => {}
                StatementKind::ConstructFunctionObject {
                    name,
                    type_variables,
                    target,
                    curry_steps,
                    curried_arguments,
                } => {}
                StatementKind::InvokeFunctionObject {
                    func_object,
                    target,
                    additional_arguments,
                } => {}
                StatementKind::Drop { variable } => {}
                StatementKind::Free { variable } => {}
                StatementKind::ConstructData {
                    name,
                    type_variables,
                    variant,
                    fields,
                    target,
                } => {}
                StatementKind::ConstructImpl {
                    aspect,
                    type_variables,
                    definitions,
                    target,
                } => {}
            }
        }
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
