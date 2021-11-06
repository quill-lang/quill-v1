use crate::{
    codegen::CodeGenContext,
    debug::source_file_debug_info,
    repr::{
        any_type::AnyTypeRepresentation, data::LLVMDataRepresentation,
        llvm_struct::LLVMStructRepresentation, LLVMRepresentations,
    },
};
use inkwell::{
    types::{BasicMetadataTypeEnum, BasicTypeEnum, FunctionType},
    AddressSpace,
};
use quill_mir::mir::{ArgumentIndex, LocalVariableName};
use quill_monomorphise::{
    mono_mir::MonomorphisedMIR, monomorphisation::MonomorphisedCurriedFunction,
};
use quill_reprs::data::FieldIndex;
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

/// Stores the representations of a monomorphised function's arguments and return type.
struct LLVMArgReprs<'ctx> {
    /// For each argument of the original Quill function, what argument index in LLVM was it mapped to?
    /// If it had no representation, this returns None.
    arg_repr_indices: Vec<Option<usize>>,
    /// The list of arguments that had representations, along with their Quill types.
    args_with_reprs: Vec<(AnyTypeRepresentation<'ctx>, Type)>,
    return_type: Option<BasicTypeEnum<'ctx>>,
    arity: u64,
    function_object: LLVMDataRepresentation<'ctx>,
}

// We allow the `fields` vec to be pushed one-by-one because it's more legible this way.
#[allow(clippy::vec_init_then_push)]
fn generate_arg_reprs<'ctx>(
    func: &MonomorphisedCurriedFunction,
    codegen: &CodeGenContext<'ctx>,
    reprs: &mut LLVMRepresentations<'_, 'ctx>,
    mir: &MonomorphisedMIR,
) -> LLVMArgReprs<'ctx> {
    let def = &mir.files[&func.func.func.source_file].definitions[&func.func.func.name]
        [&func.func.mono]
        .def;

    let args_options = (0..def.arity)
        .map(|i| {
            let info = def
                .local_variable_names
                .get(&LocalVariableName::Argument(ArgumentIndex(i)))
                .unwrap();
            let ty = replace_type_variables(
                info.ty.clone(),
                &def.type_variables,
                func.func.mono.type_parameters(),
            );
            reprs.repr(ty.clone()).map(|repr| (repr, ty))
        })
        .collect::<Vec<_>>();

    let mut arg_repr_indices = Vec::new();
    for arg in &args_options {
        arg_repr_indices.push(arg.as_ref().map(|_| arg_repr_indices.len()));
    }
    let args_with_reprs = args_options.iter().cloned().flatten().collect::<Vec<_>>();

    let return_type = replace_type_variables(
        def.return_type.clone(),
        &def.type_variables,
        func.func.mono.type_parameters(),
    );

    let descriptor = func.function_object_descriptor();
    let function_object = if let Some(repr) = reprs.get_fobj(&descriptor) {
        repr.clone()
    } else {
        let mut fields = Vec::new();

        // Add the function pointer as the first field.
        fields.push((
            ".fptr".to_string(),
            AnyTypeRepresentation::new(
                codegen,
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
                reprs.general_func_obj_ty.di_type,
            ),
            None,
        ));
        // Add the copy function as the second field.
        fields.push((
            ".copy".to_string(),
            AnyTypeRepresentation::new(
                codegen,
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
                reprs.general_func_obj_ty.di_type,
            ),
            None,
        ));
        // Add the drop function as the third field.
        fields.push((
            ".drop".to_string(),
            AnyTypeRepresentation::new(
                codegen,
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
                reprs.general_func_obj_ty.di_type,
            ),
            None,
        ));
        // Add only the arguments not pertaining to the last currying step.
        for i in 0..def.arity - func.curry.curry_steps.last().copied().unwrap_or(0) {
            if let Some((repr, ty)) =
                arg_repr_indices[i as usize].map(|i| args_with_reprs[i].clone())
            {
                fields.push((format!("field_{}", i), repr, Some(ty)));
            }
        }

        let llvm_field_types = fields
            .iter()
            .map(|(_, repr, _)| repr.llvm_type)
            .collect::<Vec<_>>();
        let llvm_repr = reprs.codegen.context.struct_type(&llvm_field_types, false);

        let di_file = source_file_debug_info(reprs.codegen, &func.func.func.source_file);

        let di_type = unsafe {
            reprs
                .codegen
                .di_builder
                .create_placeholder_derived_type(reprs.codegen.context)
        };

        let repr = LLVMDataRepresentation {
            llvm_repr: Some(LLVMStructRepresentation {
                ty: llvm_repr,
                abi_alignment: reprs.codegen.target_data().get_abi_alignment(&llvm_repr),
            }),
            di_type,
            di_file,
            range: def.range,
            name: func.func.func.name.clone(),
            field_indices: fields
                .iter()
                .enumerate()
                .map(|(i, (field_name, _repr, _ty))| {
                    (field_name.clone(), FieldIndex::Literal(i as u32))
                })
                .collect(),
            field_types: fields
                .iter()
                .filter_map(|(field_name, _repr, ty)| ty.clone().map(|ty| (field_name.clone(), ty)))
                .collect(),
        };

        // Now, define all the relevant copy and drop functions for this function object.
        // We need to make a copy/drop function for every possible amount of fields stored in this function object.
        for fields_stored in 0..=def.arity - func.curry.curry_steps.last().copied().unwrap_or(0) {
            // Unlike the drop/copy functions for known types,
            // function object drop/copy functions take/return pointers, not raw values.

            // Generate the drop function.
            {
                let func = codegen.module.add_function(
                    &format!("drop/{}#{}", descriptor, fields_stored),
                    codegen.context.void_type().fn_type(
                        &[repr
                            .llvm_repr
                            .as_ref()
                            .unwrap()
                            .ty
                            .ptr_type(AddressSpace::Generic)
                            .into()],
                        false,
                    ),
                    None,
                );
                let block = codegen.context.append_basic_block(func, "drop");
                codegen.builder.position_at_end(block);
                codegen.builder.unset_current_debug_location();

                let ptr = func.get_first_param().unwrap().into_pointer_value();
                for field_name in repr.field_indices().keys() {
                    // Check if this field has been assigned, given that we've assigned to the first `fields_stored` fields.
                    let assigned = match repr.field_indices()[field_name] {
                        FieldIndex::Heap(i) | FieldIndex::Literal(i) => {
                            // The +3 and minimum value of 3 are because fptr/drop/copy functions are the first three entries of the structure.
                            3 <= i && i < fields_stored as u32 + 3
                        }
                    };
                    if assigned {
                        let ptr_to_field = repr.load(codegen, reprs, ptr, field_name).unwrap();
                        let ty = repr.field_ty(field_name).unwrap().clone();
                        reprs.drop_ptr(ty, ptr_to_field);
                    }
                }
                repr.free_fields(codegen, ptr);
                codegen.builder.build_return(None);
            }

            // Generate the copy function.
            {
                let func = codegen.module.add_function(
                    &format!("copy/{}#{}", descriptor, fields_stored),
                    repr.llvm_repr
                        .as_ref()
                        .unwrap()
                        .ty
                        .ptr_type(AddressSpace::Generic)
                        .fn_type(
                            &[repr
                                .llvm_repr
                                .as_ref()
                                .unwrap()
                                .ty
                                .ptr_type(AddressSpace::Generic)
                                .into()],
                            false,
                        ),
                    None,
                );
                let block = codegen.context.append_basic_block(func, "copy");
                codegen.builder.position_at_end(block);
                codegen.builder.unset_current_debug_location();

                // Since we return a pointer, we must malloc the return value.
                let source = func.get_first_param().unwrap().into_pointer_value();
                let ptr = codegen
                    .builder
                    .build_call(
                        codegen.libc("malloc"),
                        &[codegen
                            .context
                            .i64_type()
                            .const_int(
                                codegen
                                    .target_data()
                                    .get_store_size(&repr.llvm_repr.as_ref().unwrap().ty),
                                false,
                            )
                            .into()],
                        "return_value_raw",
                    )
                    .try_as_basic_value()
                    .unwrap_left()
                    .into_pointer_value();
                let ptr = codegen
                    .builder
                    .build_bitcast(
                        ptr,
                        repr.llvm_repr
                            .as_ref()
                            .unwrap()
                            .ty
                            .ptr_type(AddressSpace::Generic),
                        "return_value",
                    )
                    .into_pointer_value();

                // Copy each field over into the new value.
                // Start by allocating sufficient space on the heap for the new values.
                repr.malloc_fields(codegen, reprs, ptr);

                // Copy over the fptr, copy, drop functions.
                let fptr = repr.load(codegen, reprs, source, ".fptr").unwrap();
                repr.store_ptr(codegen, reprs, ptr, fptr, ".fptr");
                let copy = repr.load(codegen, reprs, source, ".copy").unwrap();
                repr.store_ptr(codegen, reprs, ptr, copy, ".copy");
                let drop = repr.load(codegen, reprs, source, ".drop").unwrap();
                repr.store_ptr(codegen, reprs, ptr, drop, ".drop");

                // Now, for each field, copy it over.
                for field_name in repr.field_indices().keys() {
                    // Check if this field has been assigned, given that we've assigned to the first `fields_stored` fields.
                    let assigned = match repr.field_indices()[field_name] {
                        FieldIndex::Heap(i) | FieldIndex::Literal(i) => {
                            // The +3 and minimum value of 3 are because fptr/drop/copy functions are the first three entries of the structure.
                            3 <= i && i < fields_stored as u32 + 3
                        }
                    };
                    if assigned {
                        // Get the field from the source.
                        if let Some(source_field) = repr.load(codegen, reprs, source, field_name) {
                            // Copy the field.
                            let source_field_copied = reprs
                                .copy_ptr(repr.field_ty(field_name).unwrap().clone(), source_field)
                                .unwrap();
                            repr.store(codegen, reprs, ptr, source_field_copied, field_name);
                        }
                    }
                }

                codegen.builder.build_return(Some(&ptr));
            }
        }

        reprs.insert_fobj(descriptor, repr.clone());
        repr
    };

    LLVMArgReprs {
        arg_repr_indices,
        args_with_reprs,
        return_type: reprs.repr(return_type).map(|repr| repr.llvm_type),
        arity: def.arity,
        function_object,
    }
}

fn generate_llvm_type<'ctx>(
    func: &MonomorphisedCurriedFunction,
    codegen: &CodeGenContext<'ctx>,
    reprs: &mut LLVMRepresentations<'_, 'ctx>,
    mir: &MonomorphisedMIR,
) -> FunctionType<'ctx> {
    let arg_reprs = generate_arg_reprs(func, codegen, reprs, mir);

    let curry_steps_amount = func.curry.curry_steps.iter().sum::<u64>() as usize;

    // Check to see if this function is direct or indirect.
    if func.curry.direct {
        // The parameters to this function are exactly the first n arguments, where n = arity - sum(curry_steps).
        // But some of these args may not have representations, so we'll need to be careful.
        let real_args = (0..arg_reprs.arity as usize
            - func.curry.curry_steps.iter().sum::<u64>() as usize)
            .filter_map(|idx| {
                arg_reprs.arg_repr_indices[idx]
                    .map(|idx| arg_reprs.args_with_reprs[idx].0.llvm_type.into())
            })
            .collect::<Vec<_>>();

        // The return value is the function return type if curry_steps_amount == 0, else it's a function object.
        if curry_steps_amount == 0 {
            arg_reprs
                .return_type
                .map(|repr| match repr {
                    BasicTypeEnum::ArrayType(array) => array.fn_type(&real_args, false),
                    BasicTypeEnum::FloatType(float) => float.fn_type(&real_args, false),
                    BasicTypeEnum::IntType(int) => int.fn_type(&real_args, false),
                    BasicTypeEnum::PointerType(ptr) => ptr.fn_type(&real_args, false),
                    BasicTypeEnum::StructType(a_struct) => a_struct.fn_type(&real_args, false),
                    BasicTypeEnum::VectorType(vec) => vec.fn_type(&real_args, false),
                })
                .unwrap_or_else(|| codegen.context.void_type().fn_type(&real_args, false))
        } else {
            arg_reprs
                .function_object
                .llvm_repr
                .unwrap()
                .ty
                .ptr_type(AddressSpace::Generic)
                .fn_type(&real_args, false)
        }
    } else {
        // The parameters to this function are a function ptr, and then the first n arguments, where n = curry_steps[0].
        // But some of these args may not have representations, so we'll need to be careful.
        let mut real_args = vec![arg_reprs
            .function_object
            .llvm_repr
            .as_ref()
            .unwrap()
            .ty
            .ptr_type(AddressSpace::Generic)
            .into()];
        let args_already_calculated = arg_reprs.arity as usize - curry_steps_amount;
        real_args.extend(
            (args_already_calculated..args_already_calculated + func.curry.curry_steps[0] as usize)
                .filter_map(|idx| {
                    arg_reprs.arg_repr_indices[idx].map(|idx| {
                        BasicMetadataTypeEnum::from(arg_reprs.args_with_reprs[idx].0.llvm_type)
                    })
                }),
        );

        if func.curry.curry_steps.len() == 1 {
            arg_reprs
                .return_type
                .map(|repr| match repr {
                    BasicTypeEnum::ArrayType(array) => array.fn_type(&real_args, false),
                    BasicTypeEnum::FloatType(float) => float.fn_type(&real_args, false),
                    BasicTypeEnum::IntType(int) => int.fn_type(&real_args, false),
                    BasicTypeEnum::PointerType(ptr) => ptr.fn_type(&real_args, false),
                    BasicTypeEnum::StructType(a_struct) => a_struct.fn_type(&real_args, false),
                    BasicTypeEnum::VectorType(vec) => vec.fn_type(&real_args, false),
                })
                .unwrap_or_else(|| codegen.context.void_type().fn_type(&real_args, false))
        } else {
            arg_reprs
                .function_object
                .llvm_repr
                .unwrap()
                .ty
                .ptr_type(AddressSpace::Generic)
                .fn_type(&real_args, false)
        }
    }
}

/// Generates the LLVM type representing this function, then adds the type to the codegen module.
pub fn add_llvm_type<'ctx>(
    func: &MonomorphisedCurriedFunction,
    codegen: &CodeGenContext<'ctx>,
    reprs: &mut LLVMRepresentations<'_, 'ctx>,
    mir: &MonomorphisedMIR,
) {
    let ty = generate_llvm_type(func, codegen, reprs, mir);
    codegen.module.add_function(&func.to_string(), ty, None);
}
