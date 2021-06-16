use std::collections::{BTreeMap, HashMap};

use inkwell::{basic_block::BasicBlock, debug_info::DIScope, types::BasicTypeEnum, AddressSpace};

use quill_index::TypeParameter;
use quill_mir::mir::{
    ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableInfo, LocalVariableName, Operand,
    PlaceSegment, Rvalue, StatementKind, TerminatorKind,
};
use quill_parser::ConstantValue;
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::BodyCreationContext,
    func::{
        lifetime::{lifetime_end, lifetime_end_if_moved, lifetime_start},
        monomorphise::monomorphise,
        rvalue::{get_pointer_to_rvalue, get_pointer_to_rvalue_arg},
    },
    monomorphisation::{MonomorphisationParameters, MonomorphisedFunction, MonomorphisedType},
};

pub fn create_real_func_body<'ctx>(
    context: BodyCreationContext<'_, 'ctx>,
    def: &DefinitionM,
    scope: DIScope<'ctx>,
) -> BasicBlock<'ctx> {
    let mut def = monomorphise(context.reprs, &context.func, def);

    match &mut def.body {
        DefinitionBodyM::PatternMatch(cfg) => create_real_func_body_cfg(
            context,
            cfg,
            &def.local_variable_names,
            &def.type_variables,
            scope,
        ),
        DefinitionBodyM::CompilerIntrinsic => crate::intrinsics::create_real_func_body_intrinsic(
            context,
            &def.local_variable_names,
            &def.type_variables,
        ),
    }
}

fn create_real_func_body_cfg<'ctx>(
    mut ctx: BodyCreationContext<'_, 'ctx>,
    cfg: &mut ControlFlowGraph,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    type_variables: &[TypeParameter],
    scope: DIScope<'ctx>,
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
            ctx.codegen.builder.set_current_debug_location(
                ctx.codegen.context,
                ctx.codegen.di_builder.create_debug_location(
                    ctx.codegen.context,
                    stmt.range.start.line + 1,
                    stmt.range.start.col + 1,
                    scope,
                    None,
                ),
            );
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
                    lifetime_start(&ctx, local_variable_names, target, scope, stmt.range);
                    ctx.codegen
                        .builder
                        .build_memcpy(
                            target_value,
                            target_repr.abi_alignment(),
                            get_pointer_to_rvalue(
                                ctx.codegen,
                                ctx.index,
                                ctx.reprs,
                                &ctx.locals,
                                local_variable_names,
                                source,
                            )
                            .unwrap(),
                            target_repr.abi_alignment(),
                            ctx.codegen
                                .context
                                .ptr_sized_int_type(ctx.codegen.target_data(), None)
                                .const_int(target_repr.store_size(ctx.codegen) as u64, false),
                        )
                        .unwrap();
                    lifetime_end_if_moved(&ctx, local_variable_names, source);
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
                                local_variable_names,
                                rvalue,
                            )
                            .unwrap();
                            ctx.codegen
                                .builder
                                .build_load(ptr, &format!("if/{}_{}arg", mono_func, i))
                        })
                        .collect::<Vec<_>>();

                    let target_ty = local_variable_names[target].ty.clone();
                    if let Some(target_repr) = ctx.reprs.repr(target_ty.clone()) {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(target_repr.llvm_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        lifetime_start(&ctx, local_variable_names, target, scope, stmt.range);
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

                    for arg in arguments {
                        lifetime_end_if_moved(&ctx, local_variable_names, arg);
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
                                local_variable_names,
                                rvalue,
                            )
                            .unwrap();
                            ctx.codegen
                                .builder
                                .build_load(ptr, &format!("c/{}_{}arg", mono_func, i))
                        })
                        .collect::<Vec<_>>();

                    if let Some(return_type) = func.get_type().get_return_type() {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        lifetime_start(&ctx, local_variable_names, target, scope, stmt.range);
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

                    for arg in curried_arguments {
                        lifetime_end_if_moved(&ctx, local_variable_names, arg);
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
                        local_variable_names,
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
                        if let Some(ptr) = get_pointer_to_rvalue_arg(
                            ctx.codegen,
                            ctx.index,
                            ctx.reprs,
                            &ctx.locals,
                            local_variable_names,
                            arg,
                        ) {
                            args.push(ctx.codegen.builder.build_load(ptr, &format!("io/{}arg", i)))
                        }
                    }

                    if let Some(return_type) = return_ty {
                        let target_value = ctx
                            .codegen
                            .builder
                            .build_alloca(return_type, &target.to_string());
                        ctx.locals.insert(*target, target_value);
                        lifetime_start(&ctx, local_variable_names, target, scope, stmt.range);
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

                    for arg in additional_arguments {
                        lifetime_end_if_moved(&ctx, local_variable_names, arg);
                    }
                }
                StatementKind::Drop { variable } => {
                    // Depending on the type of the variable, we might need to do a variety of things.
                    // In the simplest case, where the variable is contained entirely on the stack, no action is required.
                    // If the variable contains any heap allocation, we need to free this memory (recursively).
                    // Because this can get so complicated and can recurse, we need to call a 'drop function'.
                    ctx.reprs.drop_ptr(
                        local_variable_names[variable].ty.clone(),
                        ctx.locals[variable],
                    );
                }
                StatementKind::Free { variable } => {
                    // We can signal to LLVM that we're done using this variable, and that its lifetime has ended.
                    lifetime_end(&ctx, local_variable_names, variable);
                }
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
                    lifetime_start(&ctx, local_variable_names, target, scope, stmt.range);

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
                                        local_variable_names,
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
                                        local_variable_names,
                                        field_rvalue,
                                    )
                                    .unwrap(),
                                    field_name,
                                );
                            }
                        }
                    }

                    for field_value in fields.values() {
                        lifetime_end_if_moved(&ctx, local_variable_names, field_value);
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
                    .build_unconditional_branch(blocks[other_id]);
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
                    local_variable_names,
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
                                        type_variables,
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
            TerminatorKind::SwitchConstant {
                place,
                cases,
                default,
            } => {
                let value_ptr = get_pointer_to_rvalue(
                    ctx.codegen,
                    ctx.index,
                    ctx.reprs,
                    &ctx.locals,
                    local_variable_names,
                    &Rvalue::Use(Operand::Copy(place.clone())),
                )
                .unwrap();
                let value = ctx
                    .codegen
                    .builder
                    .build_load(value_ptr, "value")
                    .into_int_value();
                let else_block = blocks[default];
                let cases = cases
                    .iter()
                    .map(|(value, block_id)| {
                        (
                            match value {
                                ConstantValue::Bool(value) => ctx
                                    .codegen
                                    .context
                                    .bool_type()
                                    .const_int(if *value { 1 } else { 0 }, false),
                                ConstantValue::Int(value) => {
                                    ctx.codegen.context.i64_type().const_int(
                                        unsafe { std::mem::transmute::<i64, u64>(*value) },
                                        false,
                                    )
                                }
                                ConstantValue::Unit => {
                                    unreachable!()
                                }
                            },
                            blocks[block_id],
                        )
                    })
                    .collect::<Vec<_>>();
                ctx.codegen.builder.build_switch(value, else_block, &cases);
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
