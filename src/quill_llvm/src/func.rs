use std::collections::{BTreeMap, HashMap};

use inkwell::{
    basic_block::BasicBlock,
    types::BasicTypeEnum,
    values::{FunctionValue, PointerValue},
    AddressSpace,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI, TypeParameter};
use quill_mir::{
    ArgumentIndex, ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableInfo,
    LocalVariableName, Operand, PlaceSegment, ProjectMIR, Rvalue, StatementKind, TerminatorKind,
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

    let block = codegen.context.append_basic_block(func_value, "entry");
    codegen.builder.position_at_end(block);

    // Check what kind of function this is.
    if func.direct {
        // A direct function contains the real function body if there are no arguments left to curry.
        if func.curry_steps.is_empty() {
            // We need to now create the real function body.
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
            let contents_block = create_real_func_body(
                BodyCreationContext {
                    codegen,
                    reprs,
                    index,
                    func,
                    func_value,
                    locals,
                },
                def,
            );
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
        } else {
            // We need to create a function object pointing to the indirect version of this function.
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

            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), fptr, ".fptr");

            codegen.builder.build_return(Some(&fobj));
        }
    } else {
        // An indirect function contains the real function body if there is only one step of curring left.
        if func.curry_steps.len() == 1 {
            // We need to create the real function body.
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
                let arg_ptr = fobj_repr.load(codegen, reprs, fobj, &format!("field_{}", arg));
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

            let contents_block = create_real_func_body(
                BodyCreationContext {
                    codegen,
                    reprs,
                    index,
                    func,
                    func_value,
                    locals,
                },
                def,
            );
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
        } else {
            // We need to update this function object to point to the next curry step.
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

            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), fptr, ".fptr");

            // Store the other arguments in the function object.
            for arg in args_supplied..args_supplied + num_args {
                let field = format!("field_{}", arg);
                if fobj_repr.has_field(&field) {
                    fobj_repr.store(
                        codegen,
                        reprs,
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

/// Contains all the useful information when generating a function body.
struct BodyCreationContext<'a, 'ctx> {
    codegen: &'a CodeGenContext<'ctx>,
    reprs: &'a Representations<'a, 'ctx>,
    index: &'a ProjectIndex,
    func: MonomorphisedFunction,
    func_value: FunctionValue<'ctx>,
    locals: HashMap<LocalVariableName, PointerValue<'ctx>>,
}

fn create_real_func_body<'ctx>(
    context: BodyCreationContext<'_, 'ctx>,
    def: &DefinitionM,
) -> BasicBlock<'ctx> {
    let mut def = monomorphise(context.reprs, &context.func, def);

    match &mut def.body {
        DefinitionBodyM::PatternMatch(cfg) => {
            create_real_func_body_cfg(context, cfg, &def.local_variable_names, &def.type_variables)
        }
        DefinitionBodyM::CompilerIntrinsic => {
            create_real_func_body_intrinsic(context, &def.local_variable_names, &def.type_variables)
        }
    }
}

fn create_real_func_body_cfg<'ctx>(
    mut ctx: BodyCreationContext<'_, 'ctx>,
    cfg: &mut ControlFlowGraph,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    type_variables: &[TypeParameter],
) -> BasicBlock<'ctx> {
    // Create new LLVM basic blocks for each MIR basic block.
    let blocks = cfg
        .basic_blocks
        .iter()
        .map(|(id, _)| {
            let block = ctx
                .codegen
                .context
                .append_basic_block(ctx.func_value, &id.to_string());
            (*id, block)
        })
        .collect::<HashMap<_, _>>();

    // Compile each MIR basic block into LLVM IR.
    for (id, block) in std::mem::take(&mut cfg.basic_blocks) {
        ctx.codegen.builder.position_at_end(blocks[&id]);

        // Handle the statements.
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign { target, source } => {
                    // Create a new local variable in LLVM for this assignment target.
                    let target_ty = local_variable_names[target].ty.clone();
                    let target_repr = ctx.reprs.repr(target_ty.clone()).unwrap();
                    let target_value = ctx
                        .codegen
                        .builder
                        .build_alloca(target_repr.llvm_type, &target.to_string());
                    ctx.locals.insert(*target, target_value);
                    ctx.codegen
                        .builder
                        .build_memcpy(
                            target_value,
                            target_repr.alignment,
                            get_pointer_to_rvalue(
                                ctx.codegen,
                                ctx.index,
                                ctx.reprs,
                                &ctx.locals,
                                &local_variable_names,
                                source,
                            )
                            .unwrap(),
                            target_repr.alignment,
                            ctx.codegen
                                .context
                                .ptr_sized_int_type(ctx.codegen.target_data(), None)
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
                    let func = ctx
                        .codegen
                        .module
                        .get_function(&mono_func.to_string())
                        .unwrap();
                    let args = arguments
                        .iter()
                        .enumerate()
                        .map(|(i, rvalue)| {
                            let ptr = get_pointer_to_rvalue(
                                ctx.codegen,
                                ctx.index,
                                ctx.reprs,
                                &ctx.locals,
                                &local_variable_names,
                                rvalue,
                            )
                            .unwrap();
                            ctx.codegen.builder.build_load(ptr, &format!("arg{}", i))
                        })
                        .collect::<Vec<_>>();

                    let target_ty = local_variable_names[target].ty.clone();
                    if let Some(target_repr) = ctx.reprs.repr(target_ty.clone()) {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(target_repr.llvm_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        let call_site_value = ctx.codegen.builder.build_call(
                            func,
                            &args,
                            &format!("{}_call", target),
                        );
                        if let Some(call_site_value) = call_site_value.try_as_basic_value().left() {
                            ctx.codegen
                                .builder
                                .build_store(target_value, call_site_value);
                        }
                    } else {
                        ctx.codegen
                            .builder
                            .build_call(func, &args, &target.to_string());
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
                    let func = ctx
                        .codegen
                        .module
                        .get_function(&mono_func.to_string())
                        .unwrap();
                    let args = curried_arguments
                        .iter()
                        .enumerate()
                        .map(|(i, rvalue)| {
                            let ptr = get_pointer_to_rvalue(
                                ctx.codegen,
                                ctx.index,
                                ctx.reprs,
                                &ctx.locals,
                                &local_variable_names,
                                rvalue,
                            )
                            .unwrap();
                            ctx.codegen.builder.build_load(ptr, &format!("arg{}", i))
                        })
                        .collect::<Vec<_>>();

                    if let Some(return_type) = func.get_type().get_return_type() {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        let call_site_value = ctx.codegen.builder.build_call(
                            func,
                            &args,
                            &format!("{}_call", target),
                        );
                        if let Some(call_site_value) = call_site_value.try_as_basic_value().left() {
                            ctx.codegen
                                .builder
                                .build_store(target_value, call_site_value);
                        }
                    } else {
                        ctx.codegen
                            .builder
                            .build_call(func, &args, &target.to_string());
                    }
                }
                StatementKind::InvokeFunctionObject {
                    func_object,
                    target,
                    additional_arguments,
                    return_type,
                    additional_argument_types,
                } => {
                    let func_object_ptr = get_pointer_to_rvalue(
                        ctx.codegen,
                        ctx.index,
                        ctx.reprs,
                        &ctx.locals,
                        &local_variable_names,
                        func_object,
                    );
                    let func_object_ptr = ctx
                        .codegen
                        .builder
                        .build_load(func_object_ptr.unwrap(), "fobj_loaded")
                        .into_pointer_value();
                    // Get the first element of this function object, which is the function pointer.
                    let fptr_raw = ctx
                        .codegen
                        .builder
                        .build_struct_gep(func_object_ptr, 0, "fptr_raw_ptr")
                        .unwrap();
                    let fptr_raw = ctx.codegen.builder.build_load(fptr_raw, "fptr_raw");
                    let return_ty = ctx
                        .reprs
                        .repr(return_type.clone())
                        .map(|repr| repr.llvm_type);
                    let mut arg_types = vec![ctx.reprs.general_func_obj_ty.llvm_type];
                    arg_types.extend(
                        additional_argument_types
                            .iter()
                            .filter_map(|ty| ctx.reprs.repr(ty.clone()))
                            .map(|repr| repr.llvm_type),
                    );
                    let func_ty = match return_ty {
                        Some(BasicTypeEnum::ArrayType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::FloatType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::IntType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::PointerType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::StructType(v)) => v.fn_type(&arg_types, false),
                        Some(BasicTypeEnum::VectorType(v)) => v.fn_type(&arg_types, false),
                        None => ctx.codegen.context.void_type().fn_type(&arg_types, false),
                    };
                    let fptr = ctx
                        .codegen
                        .builder
                        .build_bitcast(fptr_raw, func_ty.ptr_type(AddressSpace::Generic), "fptr")
                        .into_pointer_value();

                    let mut args = vec![ctx.codegen.builder.build_bitcast(
                        func_object_ptr,
                        ctx.reprs.general_func_obj_ty.llvm_type,
                        "fobj_bitcast",
                    )];
                    for (i, arg) in additional_arguments.iter().enumerate() {
                        if let Some(ptr) = get_pointer_to_rvalue(
                            ctx.codegen,
                            ctx.index,
                            ctx.reprs,
                            &ctx.locals,
                            &local_variable_names,
                            arg,
                        ) {
                            args.push(ctx.codegen.builder.build_load(ptr, &format!("arg{}", i)))
                        }
                    }

                    if let Some(return_type) = return_ty {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        let call_site_value = ctx.codegen.builder.build_call(
                            fptr,
                            &args,
                            &format!("{}_call", target),
                        );
                        if let Some(call_site_value) = call_site_value.try_as_basic_value().left() {
                            ctx.codegen
                                .builder
                                .build_store(target_value, call_site_value);
                        }
                    } else {
                        ctx.codegen
                            .builder
                            .build_call(fptr, &args, &target.to_string());
                    }
                }
                StatementKind::Drop { .. } => {}
                StatementKind::Free { .. } => {}
                StatementKind::ConstructData {
                    ty,
                    variant,
                    fields,
                    target,
                } => {
                    let target_ty = local_variable_names[target].ty.clone();
                    let target_repr = ctx.reprs.repr(target_ty.clone()).unwrap();
                    let mut target_value = ctx
                        .codegen
                        .builder
                        .build_alloca(target_repr.llvm_type, &target.to_string());
                    ctx.locals.insert(*target, target_value);

                    // If any elements of this type are indirect, `malloc` some space for the fields.
                    if let Type::Named { name, parameters } = target_ty.clone() {
                        let mono_ty = MonomorphisedType {
                            name,
                            mono: MonomorphisationParameters {
                                type_parameters: parameters,
                            },
                        };
                        if let Some(repr) = ctx.reprs.get_data(&mono_ty) {
                            repr.malloc_fields(ctx.codegen, ctx.reprs, target_value);
                        } else if let Some(repr) = ctx.reprs.get_enum(&mono_ty) {
                            let variant = &repr.variants[variant.as_ref().unwrap()];

                            target_value = ctx
                                .codegen
                                .builder
                                .build_bitcast(
                                    target_value,
                                    variant
                                        .llvm_repr
                                        .as_ref()
                                        .unwrap()
                                        .ty
                                        .ptr_type(AddressSpace::Generic),
                                    "variant_bitcast",
                                )
                                .into_pointer_value();

                            variant.malloc_fields(ctx.codegen, ctx.reprs, target_value);
                        }
                    }
                    // let mem = codegen
                    //     .builder
                    //     .build_call(
                    //         codegen.libc("malloc"),
                    //         &[codegen
                    //             .context
                    //             .i64_type()
                    //             .const_int(fobj_repr.llvm_repr.as_ref().unwrap().size as u64, false)
                    //             .into()],
                    //         "malloc_invocation",
                    //     )
                    //     .try_as_basic_value()
                    //     .unwrap_left();

                    // Memcpy all the fields into the new struct.
                    let (name, parameters) = if let Type::Named { name, parameters } = ty {
                        (name.clone(), parameters.clone())
                    } else {
                        unreachable!()
                    };

                    if let Some(variant) = variant {
                        let enum_repr = ctx
                            .reprs
                            .get_enum(&MonomorphisedType {
                                name,
                                mono: MonomorphisationParameters {
                                    type_parameters: parameters,
                                },
                            })
                            .unwrap();
                        // Assign the discriminant.
                        enum_repr.store_discriminant(ctx.codegen, ctx.reprs, target_value, variant);
                        let variant_repr = &enum_repr.variants[variant];
                        for (field_name, field_rvalue) in fields {
                            if variant_repr.has_field(field_name) {
                                variant_repr.store_ptr(
                                    ctx.codegen,
                                    ctx.reprs,
                                    target_value,
                                    get_pointer_to_rvalue(
                                        ctx.codegen,
                                        ctx.index,
                                        ctx.reprs,
                                        &ctx.locals,
                                        &local_variable_names,
                                        field_rvalue,
                                    )
                                    .unwrap(),
                                    field_name,
                                );
                            }
                        }
                    } else {
                        let data_repr = ctx
                            .reprs
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
                                    ctx.codegen,
                                    ctx.reprs,
                                    target_value,
                                    get_pointer_to_rvalue(
                                        ctx.codegen,
                                        ctx.index,
                                        ctx.reprs,
                                        &ctx.locals,
                                        &local_variable_names,
                                        field_rvalue,
                                    )
                                    .unwrap(),
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
                ctx.codegen
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
                    ctx.codegen,
                    ctx.index,
                    ctx.reprs,
                    &ctx.locals,
                    &local_variable_names,
                    &Rvalue::Use(Operand::Copy(
                        enum_place.clone().then(PlaceSegment::EnumDiscriminant),
                    )),
                )
                .unwrap();
                let discriminant = ctx
                    .codegen
                    .builder
                    .build_load(discriminant_ptr, "discriminant")
                    .into_int_value();
                let else_block = blocks[cases.values().next().unwrap()];
                let enum_repr = ctx
                    .reprs
                    .get_enum(&MonomorphisedType {
                        name: enum_name.clone(),
                        mono: MonomorphisationParameters {
                            type_parameters: enum_parameters
                                .iter()
                                .map(|ty| {
                                    replace_type_variables(
                                        ty.clone(),
                                        &type_variables,
                                        &ctx.func.mono.type_parameters,
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
                            ctx.codegen
                                .context
                                .i64_type()
                                .const_int(discriminant, false),
                            block,
                        )
                    })
                    .collect::<Vec<_>>();
                ctx.codegen
                    .builder
                    .build_switch(discriminant, else_block, &cases);
            }
            TerminatorKind::Invalid => unreachable!(),
            TerminatorKind::Return { value } => {
                if let Some(ptr) = ctx.locals.get(value) {
                    let ret_val = ctx.codegen.builder.build_load(*ptr, "result");
                    ctx.codegen.builder.build_return(Some(&ret_val));
                } else {
                    ctx.codegen.builder.build_return(None);
                }
            }
        }
    }

    blocks[&cfg.entry_point]
}

/// Generates handwritten LLVM code for intrinsics defined internally.
fn create_real_func_body_intrinsic<'ctx>(
    ctx: BodyCreationContext<'_, 'ctx>,
    _local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    _type_variables: &[TypeParameter],
) -> BasicBlock<'ctx> {
    // TODO: add an assertion that the `ctx.func.func.source_file` comes from a specific "intrinsics" module.
    let block = ctx
        .codegen
        .context
        .append_basic_block(ctx.func_value, "intrinsic");
    ctx.codegen.builder.position_at_end(block);

    match ctx.func.func.name.as_str() {
        "putchar" => {
            // This is the `putchar` intrinsic.
            // putchar : int -> unit
            let putchar = ctx.codegen.module.add_function(
                "putchar",
                ctx.codegen
                    .context
                    .i32_type()
                    .fn_type(&[ctx.codegen.context.i32_type().into()], false),
                None,
            );

            let arg0 = ctx
                .codegen
                .builder
                .build_load(
                    ctx.locals[&LocalVariableName::Argument(ArgumentIndex(0))],
                    "arg0",
                )
                .into_int_value();
            let arg0_i32 = ctx.codegen.builder.build_int_cast(
                arg0,
                ctx.codegen.context.i32_type(),
                "arg0_i32",
            );

            ctx.codegen
                .builder
                .build_call(putchar, &[arg0_i32.into()], "call_putchar");
            ctx.codegen.builder.build_return(None);
        }
        _ => {
            panic!("intrinsic {} is not defined by the compiler", ctx.func.func)
        }
    }

    block
}

/// Returns None if the rvalue had no representation.
fn get_pointer_to_rvalue<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    index: &ProjectIndex,
    reprs: &Representations<'_, 'ctx>,
    locals: &HashMap<LocalVariableName, PointerValue<'ctx>>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Option<PointerValue<'ctx>> {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => {
            if let Some(mut ptr) = locals.get(&place.local).copied() {
                let mut rvalue_ty = local_variable_names[&place.local].ty.clone();

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
                                ptr = data.load(codegen, reprs, ptr, &field).unwrap();
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
                                ptr = the_enum
                                    .load(codegen, reprs, ptr, &variant, &field)
                                    .unwrap();
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

                Some(ptr)
            } else {
                None
            }
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
                    Some(mem)
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

        for block in cfg.basic_blocks.values_mut() {
            let mut stmts = Vec::new();
            for stmt in std::mem::take(&mut block.statements) {
                let should_keep = match &stmt.kind {
                    StatementKind::Assign { target, .. }
                    | StatementKind::InstanceSymbol { target, .. }
                    | StatementKind::Apply { target, .. }
                    | StatementKind::ConstructFunctionObject { target, .. }
                    | StatementKind::CreateLambda { target, .. }
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
