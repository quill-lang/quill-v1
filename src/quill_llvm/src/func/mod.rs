use std::collections::BTreeMap;

use inkwell::{debug_info::AsDIScope, values::FunctionValue, AddressSpace};
use quill_mir::{
    mir::{ArgumentIndex, LocalVariableName},
    ProjectMIR,
};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::{BodyCreationContext, CodeGenContext},
    debug::source_file_debug_info,
    monomorphisation::{FunctionObjectDescriptor, MonomorphisedFunction},
    repr::Representations,
};

mod body;
mod lifetime;
mod monomorphise;
mod rvalue;

pub fn compile_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    mir: &ProjectMIR,
    func: MonomorphisedFunction,
) {
    // println!("func {}", func);
    let def = &mir.files[&func.func.source_file].definitions[&func.func.name];
    let func_value = codegen.module.get_function(&func.to_string()).unwrap();
    let func_object_descriptor = func.function_object_descriptor();

    let mono =
        |ty: Type| replace_type_variables(ty, &def.type_variables, func.mono.type_parameters());

    // Create debug info for the function as a whole.
    let di_file = source_file_debug_info(codegen, &func.func.source_file);
    let subprogram = codegen.di_builder.create_function(
        di_file.as_debug_info_scope(),
        &func.func.to_string(),
        Some(&func.to_string()),
        di_file,
        func.func.range.start.line + 1,
        codegen.di_builder.create_subroutine_type(
            di_file,
            reprs
                .repr(mono(def.return_type.clone()))
                .map(|repr| repr.di_type),
            &(0..def.arity)
                .map(|i| {
                    &def.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(i))].ty
                })
                .cloned()
                .filter_map(|ty| reprs.repr(mono(ty)))
                .map(|repr| repr.di_type)
                .collect::<Vec<_>>(),
            0,
        ),
        true,
        true,
        func.func.range.start.line + 1,
        0,
        false,
    );
    func_value.set_subprogram(subprogram);
    let scope = subprogram.as_debug_info_scope();

    let block = codegen.context.append_basic_block(func_value, "entry");
    codegen.builder.position_at_end(block);
    codegen.builder.unset_current_debug_location();

    // Check what kind of function this is.
    if func.direct {
        // A direct function contains the real function body if there are no arguments left to curry.
        if func.curry_steps.is_empty() {
            // We need to now create the real function body.
            let mut locals = BTreeMap::new();
            for arg in 0..def.arity {
                if reprs
                    .repr(replace_type_variables(
                        def.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(arg))]
                            .ty
                            .clone(),
                        &def.type_variables,
                        func.mono.type_parameters(),
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
            let contents_block = body::create_real_func_body(
                BodyCreationContext {
                    codegen,
                    reprs,
                    index: &mir.index,
                    func,
                    func_value,
                    locals,
                    di_file,
                },
                def,
                scope,
            );
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
        } else {
            // We need to create a function object pointing to the indirect version of this function.
            let fobj_repr = reprs.get_fobj(&func_object_descriptor).unwrap();
            let mem = codegen
                .builder
                .build_call(
                    codegen.libc("malloc"),
                    &[codegen
                        .context
                        .i64_type()
                        .const_int(
                            fobj_repr.llvm_repr.as_ref().unwrap().store_size(codegen),
                            false,
                        )
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

            let num_curry_steps = func.curry_steps.iter().sum::<u64>();

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

            // Create and store the copy function inside the new function object.
            // The drop and copy functions need to know the amount of fields that we've stored inside the function object.
            let fields_stored = def.arity - num_curry_steps;
            let copy_func_value =
                get_copy_function(codegen, &func_object_descriptor, fields_stored);
            let copy = codegen.builder.build_bitcast(
                copy_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "copy",
            );
            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), copy, ".copy");

            // Create and store the drop function inside the new function object.
            let drop_func_value =
                get_drop_function(codegen, &func_object_descriptor, fields_stored);
            let drop_fn = codegen.builder.build_bitcast(
                drop_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "drop",
            );
            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), drop_fn, ".drop");

            codegen.builder.build_return(Some(&fobj));
        }
    } else {
        // An indirect function contains the real function body if there is only one step of currying left.
        if func.curry_steps.len() == 1 {
            // We need to create the real function body.
            let mut locals = BTreeMap::new();

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
                        func.mono.type_parameters(),
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

            let contents_block = body::create_real_func_body(
                BodyCreationContext {
                    codegen,
                    reprs,
                    index: &mir.index,
                    func,
                    func_value,
                    locals,
                    di_file,
                },
                def,
                scope,
            );
            codegen.builder.position_at_end(block);
            codegen.builder.build_unconditional_branch(contents_block);
        } else {
            // We need to update this function object to point to the next curry step.
            let fobj = func_value.get_nth_param(0).unwrap();
            let fobj_repr = reprs.get_fobj(&func.function_object_descriptor()).unwrap();

            let num_curry_steps_after_call = func.curry_steps.iter().skip(1).sum::<u64>();

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

            // We also need to update the "copy" and "drop" functions in the function object.
            let fields_stored = def.arity - num_curry_steps_after_call;
            let copy_func_value =
                get_copy_function(codegen, &func_object_descriptor, fields_stored);
            let copy = codegen.builder.build_bitcast(
                copy_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "copy",
            );
            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), copy, ".copy");
            let drop_func_value =
                get_drop_function(codegen, &func_object_descriptor, fields_stored);
            let drop_fn = codegen.builder.build_bitcast(
                drop_func_value.as_global_value().as_pointer_value(),
                codegen.context.i8_type().ptr_type(AddressSpace::Generic),
                "drop",
            );
            fobj_repr.store(codegen, reprs, fobj.into_pointer_value(), drop_fn, ".drop");

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

/// Gets the "copy" function for copying a function pointer for this function.
fn get_copy_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    func_object_descriptor: &FunctionObjectDescriptor,
    fields_stored: u64,
) -> FunctionValue<'ctx> {
    codegen
        .module
        .get_function(&format!(
            "copy/{}#{}",
            func_object_descriptor.to_string(),
            fields_stored,
        ))
        .unwrap()
}

/// Gets the "drop" function for copying a function pointer for this function.
fn get_drop_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    func_object_descriptor: &FunctionObjectDescriptor,
    fields_stored: u64,
) -> FunctionValue<'ctx> {
    codegen
        .module
        .get_function(&format!(
            "drop/{}#{}",
            func_object_descriptor.to_string(),
            fields_stored,
        ))
        .unwrap()
}
