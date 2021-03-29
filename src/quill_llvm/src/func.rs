use std::collections::HashMap;

use inkwell::{
    basic_block::BasicBlock,
    types::BasicTypeEnum,
    values::{FunctionValue, PointerValue},
    AddressSpace,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_mir::{
    ArgumentIndex, DefinitionM, LocalVariableName, Operand, PlaceSegment, ProjectMIR, Rvalue,
    StatementKind, TerminatorKind,
};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::{replace_type_variables, type_check::ImmediateValue};

use crate::{
    codegen::CodeGenContext,
    repr::{MonomorphisationParameters, MonomorphisedFunction, MonomorphisedType, Representations},
};

pub fn compile_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    index: &ProjectIndex,
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
            codegen.builder.position_at_end(block);
            let mut locals = HashMap::new();
            for arg in 0..def.arity {
                if reprs
                    .repr(replace_type_variables(
                        def.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(arg))]
                            .ty
                            .clone(),
                        &def.type_variables,
                        &func.mono.type_parameters,
                    ))
                    .is_some()
                {
                    let value = func_value.get_nth_param(arg as u32).unwrap();
                    let arg_ptr = codegen
                        .builder
                        .build_alloca(value.get_type(), &format!("param{}", arg));
                    codegen.builder.build_store(arg_ptr, value);
                    locals.insert(LocalVariableName::Argument(ArgumentIndex(arg)), arg_ptr);
                }
            }
            let contents_block =
                create_real_func_body(codegen, reprs, index, func, def, func_value, locals);
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
            let block = codegen.context.append_basic_block(func_value, "entry");
            codegen.builder.position_at_end(block);
            let mut locals = HashMap::new();

            // Store the arguments given in the function pointer.
            let fobj_repr = reprs.get_fobj(&func.function_object_descriptor()).unwrap();
            let mem = func_value.get_first_param().unwrap();
            let fobj = codegen
                .builder
                .build_bitcast(
                    mem,
                    fobj_repr
                        .llvm_repr
                        .as_ref()
                        .unwrap()
                        .ty
                        .ptr_type(AddressSpace::Generic),
                    "fobj",
                )
                .into_pointer_value();
            for arg in 0..def.arity - func.curry_steps[0] {
                let arg_ptr = fobj_repr.load(codegen, fobj, &format!("field_{}", arg));
                if let Some(arg_ptr) = arg_ptr {
                    locals.insert(LocalVariableName::Argument(ArgumentIndex(arg)), arg_ptr);
                }
            }

            // Store the arguments given in the function itself.
            for arg in 0..func.curry_steps[0] {
                if reprs
                    .repr(replace_type_variables(
                        def.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(
                            def.arity - func.curry_steps[0] + arg,
                        ))]
                            .ty
                            .clone(),
                        &def.type_variables,
                        &func.mono.type_parameters,
                    ))
                    .is_some()
                {
                    let value = func_value.get_nth_param(arg as u32 + 1).unwrap();
                    let arg_ptr = codegen
                        .builder
                        .build_alloca(value.get_type(), &format!("param{}", arg));
                    codegen.builder.build_store(arg_ptr, value);
                    locals.insert(
                        LocalVariableName::Argument(ArgumentIndex(
                            def.arity - func.curry_steps[0] + arg,
                        )),
                        arg_ptr,
                    );
                }
            }

            let contents_block =
                create_real_func_body(codegen, reprs, index, func, def, func_value, locals);
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
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
    index: &ProjectIndex,
    func: MonomorphisedFunction,
    def: &DefinitionM,
    func_value: FunctionValue<'ctx>,
    mut locals: HashMap<LocalVariableName, PointerValue<'ctx>>,
) -> BasicBlock<'ctx> {
    let mut def = monomorphise(reprs, &func, def);

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

    // Compile each MIR basic block into LLVM IR.
    for (id, block) in std::mem::take(&mut def.control_flow_graph.basic_blocks) {
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
                            get_pointer_to_rvalue(codegen, index, reprs, &locals, &def, source),
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
                    let args = arguments
                        .iter()
                        .enumerate()
                        .map(|(i, rvalue)| {
                            let ptr =
                                get_pointer_to_rvalue(codegen, index, reprs, &locals, &def, rvalue);
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
                } => {
                    let mono_func = MonomorphisedFunction {
                        func: name.clone(),
                        mono: MonomorphisationParameters {
                            type_parameters: type_variables.clone(),
                        },
                        curry_steps: curry_steps.clone(),
                        direct: true,
                    };
                    let func = codegen.module.get_function(&mono_func.to_string()).unwrap();
                    let args = curried_arguments
                        .iter()
                        .enumerate()
                        .map(|(i, rvalue)| {
                            let ptr =
                                get_pointer_to_rvalue(codegen, index, reprs, &locals, &def, rvalue);
                            codegen.builder.build_load(ptr, &format!("arg{}", i))
                        })
                        .collect::<Vec<_>>();

                    if let Some(return_type) = func.get_type().get_return_type() {
                        let target_value = codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
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
                StatementKind::ApplyFunctionObject { .. } => {
                    // Remove this and just have the "invoke function object" statement?
                    unimplemented!();
                }
                StatementKind::InvokeFunctionObject {
                    func_object,
                    target,
                    additional_arguments,
                    return_type,
                    additional_argument_types,
                } => {
                    let func_object_ptr =
                        get_pointer_to_rvalue(codegen, index, reprs, &locals, &def, func_object);
                    let func_object_ptr = codegen
                        .builder
                        .build_load(func_object_ptr, "fobj_loaded")
                        .into_pointer_value();
                    // Get the first element of this function object, which is the function pointer.
                    let fptr_raw = codegen
                        .builder
                        .build_struct_gep(func_object_ptr, 0, "fptr_raw_ptr")
                        .unwrap();
                    let fptr_raw = codegen.builder.build_load(fptr_raw, "fptr_raw");
                    let return_ty = reprs.repr(return_type.clone()).map(|repr| repr.llvm_type);
                    let mut arg_types = vec![reprs.general_func_obj_ty.llvm_type];
                    arg_types.extend(
                        additional_argument_types
                            .iter()
                            .filter_map(|ty| reprs.repr(ty.clone()))
                            .map(|repr| repr.llvm_type),
                    );
                    let func_ty = match return_ty {
                        Some(BasicTypeEnum::ArrayType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::FloatType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::IntType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::PointerType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::StructType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::VectorType(v)) => v.fn_type(&arg_types, false),
                        None => codegen.context.void_type().fn_type(&arg_types, false),
                    };
                    let fptr = codegen
                        .builder
                        .build_bitcast(fptr_raw, func_ty.ptr_type(AddressSpace::Generic), "fptr")
                        .into_pointer_value();

                    let mut args = vec![codegen.builder.build_bitcast(
                        func_object_ptr,
                        reprs.general_func_obj_ty.llvm_type,
                        "fobj_bitcast",
                    )];
                    for (i, arg) in additional_arguments.iter().enumerate() {
                        args.push(codegen.builder.build_load(
                            get_pointer_to_rvalue(codegen, index, reprs, &locals, &def, arg),
                            &format!("arg{}", i),
                        ))
                    }

                    if let Some(return_type) = return_ty {
                        let target_value = codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
                        locals.insert(*target, target_value);
                        let call_site_value =
                            codegen
                                .builder
                                .build_call(fptr, &args, &format!("{}_call", target));
                        if let Some(call_site_value) = call_site_value.try_as_basic_value().left() {
                            codegen.builder.build_store(target_value, call_site_value);
                        }
                    } else {
                        codegen.builder.build_call(fptr, &args, &target.to_string());
                    }
                }
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
                                        index,
                                        reprs,
                                        &locals,
                                        &def,
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
                                        index,
                                        reprs,
                                        &locals,
                                        &def,
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
            TerminatorKind::SwitchDiscriminant {
                enum_name,
                enum_parameters,
                enum_place,
                cases,
            } => {
                let discriminant_ptr = get_pointer_to_rvalue(
                    codegen,
                    index,
                    reprs,
                    &locals,
                    &def,
                    &Rvalue::Use(Operand::Copy(
                        enum_place.clone().then(PlaceSegment::EnumDiscriminant),
                    )),
                );
                let discriminant = codegen
                    .builder
                    .build_load(discriminant_ptr, "discriminant")
                    .into_int_value();
                let else_block = blocks[cases.values().next().unwrap()];
                let enum_repr = reprs
                    .get_enum(&MonomorphisedType {
                        name: enum_name.clone(),
                        mono: MonomorphisationParameters {
                            type_parameters: enum_parameters
                                .iter()
                                .map(|ty| {
                                    replace_type_variables(
                                        ty.clone(),
                                        &def.type_variables,
                                        &func.mono.type_parameters,
                                    )
                                })
                                .collect(),
                        },
                    })
                    .unwrap();
                let cases = cases
                    .iter()
                    .map(|(name, block_id)| {
                        let discriminant = enum_repr.variant_discriminants[name];
                        let block = blocks[block_id];
                        (
                            codegen.context.i64_type().const_int(discriminant, false),
                            block,
                        )
                    })
                    .collect::<Vec<_>>();
                codegen
                    .builder
                    .build_switch(discriminant, else_block, &cases);
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
    index: &ProjectIndex,
    reprs: &Representations<'_, 'ctx>,
    locals: &HashMap<LocalVariableName, PointerValue<'ctx>>,
    def: &DefinitionM,
    rvalue: &Rvalue,
) -> PointerValue<'ctx> {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => {
            let mut ptr = locals[&place.local];
            let mut rvalue_ty = def.local_variable_names[&place.local].ty.clone();

            for segment in place.projection.clone() {
                match segment {
                    PlaceSegment::DataField { field } => {
                        // rvalue_ty is a data type.
                        if let Type::Named { name, parameters } = rvalue_ty {
                            let decl = &index[&name.source_file].types[&name.name];
                            if let TypeDeclarationTypeI::Data(datai) = &decl.decl_type {
                                rvalue_ty = datai
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .find_map(|(field_name, field_type)| {
                                        if field_name.name == field {
                                            Some(replace_type_variables(
                                                field_type.clone(),
                                                &datai.type_params,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                    .unwrap();
                            } else {
                                unreachable!()
                            }

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
                        if let Type::Named { name, parameters } = rvalue_ty {
                            let decl = &index[&name.source_file].types[&name.name];
                            if let TypeDeclarationTypeI::Enum(enumi) = &decl.decl_type {
                                rvalue_ty = enumi
                                    .variants
                                    .iter()
                                    .find(|the_variant| the_variant.name.name == variant)
                                    .unwrap()
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .find_map(|(field_name, field_type)| {
                                        if field_name.name == field {
                                            Some(replace_type_variables(
                                                field_type.clone(),
                                                &enumi.type_params,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                    .unwrap();
                            } else {
                                unreachable!()
                            }

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
                    PlaceSegment::EnumDiscriminant => {
                        // rvalue_ty is an enum type.
                        if let Type::Named { name, parameters } = rvalue_ty {
                            rvalue_ty = Type::Primitive(PrimitiveType::Int);
                            let the_enum = reprs
                                .get_enum(&MonomorphisedType {
                                    name,
                                    mono: MonomorphisationParameters {
                                        type_parameters: parameters,
                                    },
                                })
                                .unwrap();
                            ptr = the_enum.get_discriminant(codegen, ptr);
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
