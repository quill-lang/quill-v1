use std::collections::BTreeMap;

use quill_mir::mir::{DefinitionBodyM, DefinitionM, StatementKind};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{monomorphisation::MonomorphisedFunction, repr::Representations};

pub fn monomorphise<'ctx>(
    reprs: &Representations<'_, 'ctx>,
    func: &MonomorphisedFunction,
    def: &DefinitionM,
) -> DefinitionM {
    let mut result = def.clone();

    let mono = |ty: &mut Type| {
        *ty = replace_type_variables(ty.clone(), &def.type_variables, func.mono.type_parameters());
    };

    // Monomorphise all the types inside the definition.
    for info in result.local_variable_names.values_mut() {
        mono(&mut info.ty);
    }
    mono(&mut result.return_type);

    if let DefinitionBodyM::PatternMatch(cfg) = &mut result.body {
        for block in cfg.basic_blocks.values_mut() {
            for stmt in &mut block.statements {
                match &mut stmt.kind {
                    StatementKind::InstanceSymbol { type_variables, .. }
                    | StatementKind::InvokeFunction { type_variables, .. }
                    | StatementKind::ConstructFunctionObject { type_variables, .. } => {
                        for ty in type_variables {
                            mono(ty);
                        }
                    }

                    StatementKind::InvokeFunctionObject {
                        return_type,
                        additional_argument_types,
                        ..
                    } => {
                        mono(return_type);
                        for ty in additional_argument_types {
                            mono(ty);
                        }
                    }

                    StatementKind::ConstructData { type_variables, .. } => {
                        for var in type_variables {
                            mono(var);
                        }
                    }

                    _ => {}
                }
            }
        }

        // Now erase all loads and stores to/from types without a representation.
        let local_reprs = result
            .local_variable_names
            .iter()
            .map(|(name, info)| (*name, reprs.repr(info.ty.clone())))
            .collect::<BTreeMap<_, _>>();

        for block in cfg.basic_blocks.values_mut() {
            let mut stmts = Vec::new();
            for stmt in std::mem::take(&mut block.statements) {
                let should_keep = match &stmt.kind {
                    StatementKind::Assign { target, .. }
                    | StatementKind::AssignPhi { target, .. }
                    | StatementKind::InstanceSymbol { target, .. }
                    | StatementKind::Apply { target, .. }
                    | StatementKind::ConstructFunctionObject { target, .. }
                    | StatementKind::ConstructData { target, .. } => local_reprs[target].is_some(),

                    StatementKind::InvokeFunction { .. }
                    | StatementKind::InvokeFunctionObject { .. } => true,

                    StatementKind::Drop { variable } | StatementKind::Free { variable } => {
                        local_reprs[variable].is_some()
                    }

                    _ => true,
                };

                if should_keep {
                    stmts.push(stmt);
                }
            }
            block.statements = stmts;
        }
    }

    result
}
