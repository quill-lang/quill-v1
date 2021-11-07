//! Perform basic static analysis on the MIR to deduce what value
//! each local variable holds, if knowable at compile time.
//! This will add special-case functions where impl parameters are known at compile time.

use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet, VecDeque},
    fmt::Debug,
};

use quill_common::{location::Location, name::QualifiedName};
use quill_mir::mir::{
    ArgumentIndex, BasicBlockId, DefinitionBodyM, DefinitionInfo, DefinitionM, KnownValue,
    LocalVariableDetails, LocalVariableId, LocalVariableInfo, LocalVariableName, Place, Rvalue,
    StatementKind, TerminatorKind,
};
use quill_monomorphise::{
    mono_mir::{MonomorphisedDefinition, MonomorphisedMIR},
    monomorphisation::MonomorphisationParameters,
};
use quill_type::Type;

/// Must be called before the func_objects pass,
/// and before special cases are generated.
pub fn analyse_values(mir: &mut MonomorphisedMIR) {
    // Run static analysis on each definition.
    let mut analysis_queue = mir
        .files
        .iter()
        .map(|(file_name, file)| {
            file.definitions
                .iter()
                .map(move |(name, defs)| {
                    defs.keys().map(move |params| FunctionDescriptor {
                        name: QualifiedName {
                            source_file: file_name.clone(),
                            name: name.clone(),
                            range: Location { line: 0, col: 0 }.into(),
                        },
                        params: params.clone(),
                    })
                })
                .flatten()
        })
        .flatten()
        .collect::<VecDeque<_>>();
    // The set of functions that have appeared in the analysis queue at least once before.
    let mut analysed_functions = analysis_queue.iter().cloned().collect::<BTreeSet<_>>();

    // If a function A calls another function B,
    // then the return value contains a mapping B -> A.
    // This means that when info about B is deduced, we can find all A that depend on this new info.
    let mut function_dependencies =
        BTreeMap::<FunctionDescriptor, BTreeSet<FunctionDescriptor>>::new();

    // The arities of each function are stored here.
    // Known return values are only used if we're calling a 0-ary function, since otherwise we won't actually get the return value when we call it -
    // just a curried function object.
    // Arities of special case functions are deduced by subtracting the number of special case arguments from the arity of the base function.
    let arities = mir
        .files
        .iter()
        .map(|(file_name, file)| {
            file.definitions.iter().map(move |(name, defs)| {
                (
                    QualifiedName {
                        source_file: file_name.clone(),
                        name: name.clone(),
                        range: Location { line: 0, col: 0 }.into(),
                    },
                    defs.iter().next().unwrap().1.def.arity,
                )
            })
        })
        .flatten()
        .collect::<BTreeMap<_, _>>();

    let mut known_return_values = BTreeMap::new();

    while let Some(desc) = analysis_queue.pop_front() {
        let defs = mir
            .files
            .get_mut(&desc.name.source_file)
            .unwrap()
            .definitions
            .get_mut(&desc.name.name)
            .unwrap();
        let def = if let Some(def) = defs.get_mut(&desc.params) {
            def
        } else {
            // We're creating a special case definition.
            // Get the equivalent non-special-case definition and create a special case definition based upon it.
            let original = defs
                .get(&MonomorphisationParameters::new(
                    desc.params.type_parameters().to_vec(),
                ))
                .unwrap();

            // Convert the definition into a special case.
            let special_case = convert_special_case(
                original.def.clone(),
                desc.params.special_case_arguments().to_vec(),
                mir,
            );

            // Reborrow defs.
            let defs = mir
                .files
                .get_mut(&desc.name.source_file)
                .unwrap()
                .definitions
                .get_mut(&desc.name.name)
                .unwrap();

            // Insert it into the definitions set and retrieve a reference to it.
            defs.insert(
                desc.params.clone(),
                MonomorphisedDefinition {
                    def: special_case,
                    curry_possibilities: BTreeSet::new(),
                },
            );
            defs.get_mut(&desc.params).unwrap()
        };

        let result = analyse_values_def(&mut def.def, &arities, &known_return_values);
        analysed_functions.insert(desc.clone());

        for dep_def in result.defs_required {
            function_dependencies
                .entry(dep_def.clone())
                .or_default()
                .insert(desc.clone());
            if analysed_functions.insert(dep_def.clone()) {
                analysis_queue.push_back(dep_def)
            }
        }

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
                analysis_queue.extend(
                    function_dependencies
                        .get(&desc)
                        .map(|val| val.iter())
                        .into_iter()
                        .flatten()
                        .cloned(),
                );
            }
        }
    }

    // Now that values are known, replace the MIR of each assignment with
    // new MIR that initialises each runtime value to the compile-time known value.
    // This will inevitably introduce dead code, which will need to be eliminated later.
    for analysed_function in analysed_functions {
        let defs = mir
            .files
            .get(&analysed_function.name.source_file)
            .unwrap()
            .definitions
            .get(&analysed_function.name.name)
            .unwrap();
        let mut def = defs.get(&analysed_function.params).unwrap().clone();
        propagate_known_values(&mut def.def, |name, tys, vals| {
            let v = &mir.files[&name.source_file].definitions[&name.name]
                [&MonomorphisationParameters::new(tys.to_vec()).with_args(vals.iter().cloned())];
            DefinitionInfo {
                arity: v.def.arity,
                symbol_type: v.def.symbol_type(),
            }
        });

        // Replace the definition, with updated values, back in the map.
        let defs = mir
            .files
            .get_mut(&analysed_function.name.source_file)
            .unwrap()
            .definitions
            .get_mut(&analysed_function.name.name)
            .unwrap();
        *defs.get_mut(&analysed_function.params).unwrap() = def;
    }
}

/// Convert variables' known values into MIR which generates the known value.
/// This will inevitably introduce dead code, which will need to be eliminated later.
fn propagate_known_values(
    def: &mut DefinitionM,
    definition_infos: impl Clone + Fn(&QualifiedName, &[Type], &[KnownValue]) -> DefinitionInfo,
) {
    let cfg = if let DefinitionBodyM::PatternMatch(cfg) = &mut def.body {
        cfg
    } else {
        return;
    };

    let mut next_local_id = def
        .local_variable_names
        .iter()
        .fold(0, |num, (local_name, _)| {
            if let LocalVariableName::Local(LocalVariableId(n)) = local_name {
                std::cmp::max(num, *n)
            } else {
                num
            }
        })
        + 1;

    for block in cfg.basic_blocks.values_mut() {
        let mut new_statements = Vec::new();
        for stmt in std::mem::take(&mut block.statements) {
            match &stmt.kind {
                StatementKind::Assign { target, .. }
                | StatementKind::AssignPhi { target, .. }
                | StatementKind::InstanceSymbol { target, .. }
                | StatementKind::Apply { target, .. }
                | StatementKind::InvokeFunction { target, .. }
                | StatementKind::ConstructFunctionObject { target, .. }
                | StatementKind::InvokeFunctionObject { target, .. }
                | StatementKind::ConstructData { target, .. }
                | StatementKind::ConstructImpl { target, .. } => {
                    // If the target is known, replace this statement with code that
                    // instantiates the known value.
                    if let Some(known_value) = &def.local_variable_names[target].details.value {
                        let result = known_value.clone().generate(
                            *target,
                            next_local_id,
                            &mut def.local_variable_names,
                            definition_infos.clone(),
                        );
                        new_statements.extend(result.statements);
                        next_local_id = result.next_local_id;
                    } else {
                        new_statements.push(stmt);
                    }
                }

                StatementKind::Drop { .. } | StatementKind::Free { .. } => {
                    new_statements.push(stmt);
                }
            }
        }
        block.statements = new_statements;
    }
}

/// Convert a definition into a special case definition.
/// Removes the first few arguments, replacing them with the new special case arguments.
fn convert_special_case(
    mut def: DefinitionM,
    special_case_arguments: Vec<KnownValue>,
    mir: &MonomorphisedMIR,
) -> DefinitionM {
    let cfg = if let DefinitionBodyM::PatternMatch(cfg) = &mut def.body {
        cfg
    } else {
        return def;
    };

    let mut next_local_id = def
        .local_variable_names
        .iter()
        .fold(0, |num, (local_name, _)| {
            if let LocalVariableName::Local(LocalVariableId(n)) = local_name {
                std::cmp::max(num, *n)
            } else {
                num
            }
        })
        + 1;
    // The local variable id for special case argument `i` is `special_case_base_id + i`.
    let special_case_base_id = next_local_id;

    for (i, value) in special_case_arguments.iter().enumerate() {
        // Create a new local variable with this value.
        def.local_variable_names.insert(
            LocalVariableName::Local(LocalVariableId(next_local_id)),
            LocalVariableInfo {
                range: Location { line: 0, col: 0 }.into(),
                ty: def.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(i as u64))]
                    .ty
                    .clone(),
                details: LocalVariableDetails {
                    name: Some("special case argument".to_string()),
                    value: Some(value.clone()),
                },
            },
        );
        next_local_id += 1;
    }

    // Now that we've created the locals, let's replace all uses of arguments with these locals.
    for (i, _) in special_case_arguments.iter().enumerate() {
        cfg.replace_uses(
            LocalVariableName::Argument(ArgumentIndex(i as u64)),
            LocalVariableName::Local(LocalVariableId(special_case_base_id + i as u64)),
        );
    }

    // Now initialise the new locals with their known values.
    for (i, value) in special_case_arguments.iter().enumerate() {
        let gen_result = value.generate(
            LocalVariableName::Local(LocalVariableId(special_case_base_id + i as u64)),
            next_local_id,
            &mut def.local_variable_names,
            |name, type_variables, special_case_arguments| {
                let def = &mir.files[&name.source_file].definitions[&name.name]
                    [&MonomorphisationParameters::new(type_variables.to_vec())
                        .with_args(special_case_arguments.to_vec())];
                DefinitionInfo {
                    arity: def.def.arity,
                    symbol_type: def.def.symbol_type(),
                }
            },
        );

        // Add the statements initialising the variable to the start of the control flow graph.
        cfg.basic_blocks
            .get_mut(&BasicBlockId(0))
            .unwrap()
            .statements
            .splice(0..0, gen_result.statements);
        next_local_id = gen_result.next_local_id;
    }

    // Move all the arguments to the function along.
    for i in special_case_arguments.len() as u64..def.arity {
        cfg.replace_uses(
            LocalVariableName::Argument(ArgumentIndex(i)),
            LocalVariableName::Argument(ArgumentIndex(i - special_case_arguments.len() as u64)),
        );
        let info = def
            .local_variable_names
            .remove(&LocalVariableName::Argument(ArgumentIndex(i)))
            .unwrap();
        def.local_variable_names.insert(
            LocalVariableName::Argument(ArgumentIndex(i - special_case_arguments.len() as u64)),
            info,
        );
    }
    // Remove redundant locals from the local variables list.
    for i in (def.arity - special_case_arguments.len() as u64)..def.arity {
        def.local_variable_names
            .remove(&LocalVariableName::Argument(ArgumentIndex(i)));
    }
    def.arity -= special_case_arguments.len() as u64;
    // TODO: we should protect against supplying more args than the arity of the function

    def
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

struct AnalysisResult {
    return_value: Option<KnownValue>,
    /// When analysing, we might depend on other definitions.
    /// Their descriptors are stored here.
    /// If a descriptor is a special case, the caller is responsible for *creating* the special case definition
    /// if it does not yet exist.
    defs_required: BTreeSet<FunctionDescriptor>,
}

/// Work out what value each variable holds, if known at compile time.
fn analyse_values_def(
    def: &mut DefinitionM,
    arities: &BTreeMap<QualifiedName, u64>,
    known_return_values: &BTreeMap<FunctionDescriptor, KnownValue>,
) -> AnalysisResult {
    // Run through the control flow graph and work out what value each variable might hold.
    let cfg = match &mut def.body {
        DefinitionBodyM::PatternMatch(cfg) => cfg,
        DefinitionBodyM::CompilerIntrinsic => {
            return AnalysisResult {
                return_value: None,
                defs_required: BTreeSet::new(),
            }
        }
    };

    let mut defs_required = BTreeSet::new();
    let mut type_of_def = |desc: FunctionDescriptor| -> KnownValue {
        match arities
            .get(&desc.name)
            .map(|x| x - desc.params.special_case_arguments().len() as u64)
        {
            Some(0) => {
                let ty = known_return_values.get(&desc).cloned().unwrap_or_else(|| {
                    KnownValue::Instantiate {
                        name: desc.name.clone(),
                        type_variables: desc.params.type_parameters().to_vec(),
                        special_case_arguments: desc.params.special_case_arguments().to_vec(),
                    }
                });
                defs_required.insert(desc);
                ty
            }
            _ => {
                let ty = KnownValue::Instantiate {
                    name: desc.name.clone(),
                    type_variables: desc.params.type_parameters().to_vec(),
                    special_case_arguments: desc.params.special_case_arguments().to_vec(),
                };
                defs_required.insert(desc);
                ty
            }
        }
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
                StatementKind::InstanceSymbol {
                    name,
                    type_variables,
                    special_case_arguments,
                    target,
                } => {
                    let known_value = type_of_def(FunctionDescriptor {
                        name: name.clone(),
                        params: MonomorphisationParameters::new(type_variables.clone())
                            .with_args(special_case_arguments.clone()),
                    });

                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(known_value);
                }
                StatementKind::Apply {
                    argument,
                    function,
                    target,
                } => {
                    // In the general case, we can't compute the result of a function call statically.
                    // However, if the argument is an impl, and the function is known, we can make a special case function
                    // for this specific case.
                    let (name, type_variables, mut special_case_arguments) =
                        if let Some(KnownValue::Instantiate {
                            name,
                            type_variables,
                            special_case_arguments,
                        }) = get_value_of_rvalue(&def.local_variable_names, &*function)
                        {
                            (name, type_variables, special_case_arguments)
                        } else {
                            continue 'stmt_loop;
                        };

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

                    let value = type_of_def(FunctionDescriptor {
                        name,
                        params: MonomorphisationParameters::new(type_variables)
                            .with_args(special_case_arguments),
                    });

                    def.local_variable_names
                        .get_mut(target)
                        .unwrap()
                        .details
                        .value = Some(value);
                }
                StatementKind::InvokeFunction { .. } => {
                    // This is created by the func_objects pass.
                    // This analysis step happens before func_objects.
                    panic!("func objects has already been run");
                }
                StatementKind::ConstructFunctionObject { .. } => {
                    panic!("func objects has already been run");
                }
                StatementKind::InvokeFunctionObject { .. } => {
                    panic!("func objects has already been run");
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

    AnalysisResult {
        return_value,
        defs_required,
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
