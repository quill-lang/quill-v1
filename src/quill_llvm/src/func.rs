use inkwell::AddressSpace;
use quill_mir::ProjectMIR;

use crate::{
    codegen::CodeGenContext,
    repr::{MonomorphisedFunction, Representations},
};

pub fn compile_function<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    reprs: &Representations<'_, 'ctx>,
    mir: &ProjectMIR,
    func: MonomorphisedFunction,
) {
    let func_value = codegen.module.get_function(&func.to_string()).unwrap();

    // Check what kind of function this is.
    if func.direct {
        // A direct function contains the real function body if there are no arguments left to curry.
        if func.curry_steps.is_empty() {
            // We need to now create the real function body.
        } else {
            // We need to create a function object pointing to the indirect version of this function.
            let block = codegen.context.append_basic_block(func_value, "entry");
            codegen.builder.position_at_end(block);

            let fobj_repr = reprs.fobj(&func.function_object_descriptor()).unwrap();
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
        }
    }
}
