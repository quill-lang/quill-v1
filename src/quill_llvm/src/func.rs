use std::collections::HashMap;

use inkwell::{
    basic_block::BasicBlock,
    values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue},
    AddressSpace,
};
use quill_mir::{
    ArgumentIndex, BasicBlockId, ControlFlowGraph, DefinitionM, LocalVariableName, Operand,
    PlaceSegment, ProjectMIR, Rvalue, StatementKind, TerminatorKind,
};
use quill_type::Type;
use quill_type_deduce::{replace_type_variables, type_check::ImmediateValue};

use crate::{
    codegen::CodeGenContext,
    repr::{
        AnyTypeRepresentation, MonomorphisationParameters, MonomorphisedFunction,
        MonomorphisedType, Representations,
    },
};

pub fn compile_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    mir: &ProjectMIR,
    func: MonomorphisedFunction,
) {
    let def = &mir.files[&func.func.source_file].definitions[&func.func.name];
    let func_value = codegen.module.get_function(&func.to_string()).unwrap();

    // Check what kind of function this is.
    if func.direct {
        // A direct function contains the real function body if there are no arguments left to curry.
        if func.curry_steps.is_empty() {
            // We need to now create the real function body.
            let block = codegen.context.append_basic_block(func_value, "entry");
            let contents_block = create_real_func_body(codegen, reprs, mir, func, def, func_value);
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
        } else {
            // We need to create a function object pointing to the indirect version of this function.
            let block = codegen.context.append_basic_block(func_value, "entry");
            codegen.builder.position_at_end(block);

            let fobj_repr = reprs.get_fobj(&func.function_object_descriptor()).unwrap();
            let mem = codegen
                .builder
                .build_call(
                    codegen.libc("malloc"),
                    &[codegen
                        .context
                        .i64_type()
                        .const_int(fobj_repr.llvm_repr.as_ref().unwrap().size as u64, false)
                        .into()],
                    "malloc_invocation",
                )
                .try_as_basic_value()
                .unwrap_left();

            // Bitcast to the right type.
            let fobj = codegen.builder.build_bitcast(
                mem,
                fobj_repr
                    .llvm_repr
                    .as_ref()
                    .unwrap()
                    .ty
                    .ptr_type(AddressSpace::Generic),
                "fobj",
            );

            // Store the next function's address inside the new function object.
            let mut next_func = func;
            next_func.direct = false;
            let next_func_value = codegen.module.get_function(&next_func.to_string()).unwrap();

            let fptr = codegen.builder.build_bitcast(
                next_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "fptr",
            );

            fobj_repr.store(codegen, fobj.into_pointer_value(), fptr, ".fptr");

            codegen.builder.build_return(Some(&fobj));
        }
    } else {
        // An indirect function contains the real function body if there is only one step of curring left.
        if func.curry_steps.len() == 1 {
            // We need to create the real function body.
        } else {
            // We need to update this function object to point to the next curry step.
            let block = codegen.context.append_basic_block(func_value, "entry");
            codegen.builder.position_at_end(block);

            let fobj = func_value.get_nth_param(0).unwrap();
            let fobj_repr = reprs.get_fobj(&func.function_object_descriptor()).unwrap();

            // Store the next function's address inside the new function object.
            let mut next_func = func;
            let args_not_supplied = next_func.curry_steps.iter().sum::<u64>();
            let args_supplied = def.arity - args_not_supplied;
            let num_args = next_func.curry_steps.remove(0);
            let next_func_value = codegen.module.get_function(&next_func.to_string()).unwrap();

            let fptr = codegen.builder.build_bitcast(
                next_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "fptr",
            );

            fobj_repr.store(codegen, fobj.into_pointer_value(), fptr, ".fptr");

            // Store the other arguments in the function object.
            for arg in args_supplied..args_supplied + num_args {
                let field = format!("field_{}", arg);
                if fobj_repr.has_field(&field) {
                    println!("Processing {} at {}", field, arg - args_supplied + 1);
                    fobj_repr.store(
                        codegen,
                        fobj.into_pointer_value(),
                        func_value
                            .get_nth_param((arg - args_supplied + 1) as u32)
                            .unwrap(),
                        &field,
                    );
                }
            }

            codegen.builder.build_return(Some(&fobj));
        }
    }
}

fn create_real_func_body<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    mir: &ProjectMIR,
    func: MonomorphisedFunction,
    def: &DefinitionM,
    func_value: FunctionValue<'ctx>,
) -> BasicBlock<'ctx> {
    println!("Compiling MIR");
    println!("{}", def);
    let def = monomorphise(reprs, &func, def);
    println!("Monomorphised:");
    println!("{}", def);

    // Create new LLVM basic blocks for each MIR basic block.
    let blocks = def
        .control_flow_graph
        .basic_blocks
        .iter()
        .map(|(id, _)| {
            let block = codegen
                .context
                .append_basic_block(func_value, &id.to_string());
            (*id, block)
        })
        .collect::<HashMap<_, _>>();

    let mut locals = HashMap::new();

    // Compile each MIR basic block into LLVM IR.
    for (id, block) in def.control_flow_graph.basic_blocks {
        codegen.builder.position_at_end(blocks[&id]);

        // Handle the statements.
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign { target, source } => {
                    // Create a new local variable in LLVM for this assignment target.
                    let target_ty = def.local_variable_names[target].ty.clone();
                    let target_repr = reprs.repr(target_ty.clone()).unwrap();
                    let target_value = codegen
                        .builder
                        .build_alloca(target_repr.llvm_type, &target.to_string());
                    locals.insert(*target, target_value);
                    codegen
                        .builder
                        .build_memcpy(
                            target_value,
                            target_repr.alignment,
                            get_pointer_to_rvalue(codegen, reprs, &locals, &target_ty, source),
                            target_repr.alignment,
                            codegen
                                .context
                                .ptr_sized_int_type(codegen.target_data(), None)
                                .const_int(target_repr.size as u64, false),
                        )
                        .unwrap();
                }
                StatementKind::InvokeFunction {
                    name,
                    type_variables,
                    target,
                    arguments,
                } => {
                    let mono_func = MonomorphisedFunction {
                        func: name.clone(),
                        mono: MonomorphisationParameters {
                            type_parameters: type_variables.clone(),
                        },
                        curry_steps: Vec::new(),
                        direct: true,
                    };
                    let func = codegen.module.get_function(&mono_func.to_string()).unwrap();
                    let inner_def = &mir.files[&name.source_file].definitions[&name.name];
                    let args = arguments
                        .iter()
                        .enumerate()
                        .map(|(i, rvalue)| {
                            let rvalue_info = &inner_def.local_variable_names
                                [&LocalVariableName::Argument(ArgumentIndex(i as u64))];
                            let rvalue_ty = replace_type_variables(
                                rvalue_info.ty.clone(),
                                &inner_def.type_variables,
                                type_variables,
                            );
                            let ptr =
                                get_pointer_to_rvalue(codegen, reprs, &locals, &rvalue_ty, rvalue);
                            codegen.builder.build_load(ptr, &format!("arg{}", i))
                        })
                        .collect::<Vec<_>>();

                    let target_ty = def.local_variable_names[target].ty.clone();
                    if let Some(target_repr) = reprs.repr(target_ty.clone()) {
                        let target_value = codegen
                            .builder
                            .build_alloca(target_repr.llvm_type, &target.to_string());
                        locals.insert(*target, target_value);
                        let call_site_value =
                            codegen
                                .builder
                                .build_call(func, &args, &format!("{}_call", target));
                        if let Some(call_site_value) = call_site_value.try_as_basic_value().left() {
                            codegen.builder.build_store(target_value, call_site_value);
                        }
                    } else {
                        codegen.builder.build_call(func, &args, &target.to_string());
                    }
                }
                StatementKind::ConstructFunctionObject {
                    name,
                    type_variables,
                    target,
                    curry_steps,
                    curried_arguments,
                } => {}
                StatementKind::ApplyFunctionObject {
                    argument,
                    function,
                    target,
                } => {}
                StatementKind::InvokeFunctionObject {
                    func_object,
                    target,
                    additional_arguments,
                } => {}
                StatementKind::Drop { variable } => {}
                StatementKind::Free { variable } => {}
                StatementKind::ConstructData {
                    ty,
                    variant,
                    fields,
                    target,
                } => {
                    let target_ty = def.local_variable_names[target].ty.clone();
                    let target_repr = reprs.repr(target_ty.clone()).unwrap();
                    let target_value = codegen
                        .builder
                        .build_alloca(target_repr.llvm_type, &target.to_string());
                    locals.insert(*target, target_value);

                    // Memcpy all the fields into the new struct.
                    let (name, parameters) = if let Type::Named { name, parameters } = ty {
                        (name.clone(), parameters.clone())
                    } else {
                        unreachable!()
                    };

                    if let Some(variant) = variant {
                        let enum_repr = reprs
                            .get_enum(&MonomorphisedType {
                                name,
                                mono: MonomorphisationParameters {
                                    type_parameters: parameters,
                                },
                            })
                            .unwrap();
                        // Assign the discriminant.
                        enum_repr.store_discriminant(codegen, target_value, variant);
                        let variant_repr = &enum_repr.variants[variant];
                        for (field_name, field_rvalue) in fields {
                            if variant_repr.has_field(field_name) {
                                variant_repr.store_ptr(
                                    codegen,
                                    target_value,
                                    get_pointer_to_rvalue(
                                        codegen,
                                        reprs,
                                        &locals,
                                        &target_ty,
                                        field_rvalue,
                                    ),
                                    field_name,
                                );
                            }
                        }
                    } else {
                        let data_repr = reprs
                            .get_data(&MonomorphisedType {
                                name,
                                mono: MonomorphisationParameters {
                                    type_parameters: parameters,
                                },
                            })
                            .unwrap();
                        for (field_name, field_rvalue) in fields {
                            if data_repr.has_field(field_name) {
                                data_repr.store(
                                    codegen,
                                    target_value,
                                    get_pointer_to_rvalue(
                                        codegen,
                                        reprs,
                                        &locals,
                                        &target_ty,
                                        field_rvalue,
                                    ),
                                    field_name,
                                );
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Handle the terminator.
        match &block.terminator.kind {
            TerminatorKind::Goto(other_id) => {
                codegen
                    .builder
                    .build_unconditional_branch(blocks[&other_id]);
            }
            TerminatorKind::SwitchDiscriminator {
                enum_name,
                enum_place,
                cases,
            } => {
                // TODO make this work
                codegen
                    .builder
                    .build_unconditional_branch(blocks[&cases.iter().next().unwrap().1]);
            }
            TerminatorKind::Invalid => unreachable!(),
            TerminatorKind::Return { value } => {
                if let Some(ptr) = locals.get(value) {
                    let ret_val = codegen.builder.build_load(*ptr, "result");
                    codegen.builder.build_return(Some(&ret_val));
                } else {
                    codegen.builder.build_return(None);
                }
            }
        }
    }

    blocks[&def.entry_point]
}

fn get_pointer_to_rvalue<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    locals: &HashMap<LocalVariableName, PointerValue<'ctx>>,
    rvalue_ty: &Type,
    rvalue: &Rvalue,
) -> PointerValue<'ctx> {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => {
            let mut ptr = locals[&place.local];

            for segment in place.projection.clone() {
                match segment {
                    PlaceSegment::DataField { field } => {
                        // rvalue_ty is a data type.
                        if let Type::Named { name, parameters } = rvalue_ty.clone() {
                            let data = reprs
                                .get_data(&MonomorphisedType {
                                    name,
                                    mono: MonomorphisationParameters {
                                        type_parameters: parameters,
                                    },
                                })
                                .unwrap();
                            ptr = data.load(codegen, ptr, &field).unwrap();
                        } else {
                            unreachable!()
                        }
                    }
                    PlaceSegment::EnumField { variant, field } => {
                        // rvalue_ty is an enum type.
                        if let Type::Named { name, parameters } = rvalue_ty.clone() {
                            let the_enum = reprs
                                .get_enum(&MonomorphisedType {
                                    name,
                                    mono: MonomorphisationParameters {
                                        type_parameters: parameters,
                                    },
                                })
                                .unwrap();
                            ptr = the_enum.load(codegen, ptr, &variant, &field).unwrap();
                        } else {
                            unreachable!()
                        }
                    }
                }
            }

            ptr
        }
        Rvalue::Use(Operand::Constant(constant)) => {
            // Alloca the constant, then make a pointer to it.
            match constant {
                ImmediateValue::Unit => unreachable!(),
                ImmediateValue::Int(value) => {
                    let mem = codegen
                        .builder
                        .build_alloca(codegen.context.i64_type(), "constant");
                    codegen.builder.build_store(
                        mem,
                        codegen
                            .context
                            .i64_type()
                            .const_int(unsafe { std::mem::transmute::<i64, u64>(*value) }, true),
                    );
                    mem
                }
            }
        }
    }
}

fn monomorphise<'ctx>(
    reprs: &Representations<'_, 'ctx>,
    func: &MonomorphisedFunction,
    def: &DefinitionM,
) -> DefinitionM {
    let mut result = def.clone();

    let mono = |ty: &mut Type| {
        *ty = replace_type_variables(ty.clone(), &def.type_variables, &func.mono.type_parameters);
    };

    // Monomorphise all the types inside the definition.
    for info in result.local_variable_names.values_mut() {
        mono(&mut info.ty);
    }
    for block in result.control_flow_graph.basic_blocks.values_mut() {
        for stmt in &mut block.statements {
            match &mut stmt.kind {
                StatementKind::InstanceSymbol { type_variables, .. }
                | StatementKind::InvokeFunction { type_variables, .. }
                | StatementKind::ConstructFunctionObject { type_variables, .. } => {
                    for ty in type_variables {
                        mono(ty);
                    }
                }

                StatementKind::CreateLambda { ty, .. }
                | StatementKind::ConstructData { ty, .. } => {
                    mono(ty);
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
        .collect::<HashMap<_, _>>();

    for block in result.control_flow_graph.basic_blocks.values_mut() {
        let mut stmts = Vec::new();
        for stmt in std::mem::take(&mut block.statements) {
            let should_keep = match &stmt.kind {
                StatementKind::Assign { target, .. }
                | StatementKind::InstanceSymbol { target, .. }
                | StatementKind::Apply { target, .. }
                | StatementKind::InvokeFunction { target, .. }
                | StatementKind::ConstructFunctionObject { target, .. }
                | StatementKind::ApplyFunctionObject { target, .. }
                | StatementKind::InvokeFunctionObject { target, .. }
                | StatementKind::CreateLambda { target, .. }
                | StatementKind::ConstructData { target, .. } => local_reprs[target].is_some(),

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

    result
}
