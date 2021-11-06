use std::collections::BTreeMap;

use inkwell::{
    debug_info::{DIFlagsConstants, DIScope},
    AddressSpace,
};
use quill_common::location::Range;
use quill_mir::mir::{LocalVariableInfo, LocalVariableName, Rvalue};

use crate::codegen::BodyCreationContext;

/// The range given is the range where the name was defined.
pub fn lifetime_start<'ctx>(
    ctx: &BodyCreationContext<'_, 'ctx>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    variable: &LocalVariableName,
    scope: DIScope<'ctx>,
    range: Range,
) {
    let ptr = if let Some(ptr) = ctx.locals.get(variable) {
        *ptr
    } else {
        return;
    };

    let info = local_variable_names[variable].clone();
    let repr = ctx.reprs.repr(info.ty.clone()).unwrap();
    let name = info.details.name.unwrap_or_else(|| variable.to_string());

    // Initialise debug info for the variable.
    // TODO: make the scope be the actual scope of the variable.
    // println!("ty: {:?}", repr.llvm_type);
    ctx.codegen.di_builder.insert_declare_at_end(
        ptr,
        Some(ctx.codegen.di_builder.create_auto_variable(
            scope,
            &name,
            ctx.di_file,
            range.start.line + 1,
            repr.di_type,
            true,
            DIFlagsConstants::ZERO,
            repr.abi_alignment() * 8,
        )),
        None,
        ctx.codegen.di_builder.create_debug_location(
            ctx.codegen.context,
            range.start.line + 1,
            range.start.col + 1,
            scope,
            None,
        ),
        ctx.codegen.builder.get_insert_block().unwrap(),
    );

    // Start the variable's lifetime.
    let ptr = ctx.codegen.builder.build_bitcast(
        ptr,
        ctx.codegen
            .context
            .i8_type()
            .ptr_type(AddressSpace::Generic),
        "lifetime_start_obj",
    );
    let size = repr.store_size(ctx.codegen);
    ctx.codegen.builder.build_call(
        ctx.codegen
            .module
            .get_function("llvm.lifetime.start.p0i8")
            .unwrap(),
        &[
            ctx.codegen
                .context
                .i64_type()
                .const_int(size as u64, false)
                .into(),
            ptr.into(),
        ],
        "lifetime_start",
    );
}

pub fn lifetime_end<'ctx>(
    ctx: &BodyCreationContext<'_, 'ctx>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    variable: &LocalVariableName,
) {
    let ptr = if let Some(ptr) = ctx.locals.get(variable) {
        *ptr
    } else {
        return;
    };
    let ptr = ctx.codegen.builder.build_bitcast(
        ptr,
        ctx.codegen
            .context
            .i8_type()
            .ptr_type(AddressSpace::Generic),
        "lifetime_end_obj",
    );
    let size = ctx
        .reprs
        .repr(local_variable_names[variable].ty.clone())
        .unwrap()
        .store_size(ctx.codegen);
    ctx.codegen.builder.build_call(
        ctx.codegen
            .module
            .get_function("llvm.lifetime.end.p0i8")
            .unwrap(),
        &[
            ctx.codegen
                .context
                .i64_type()
                .const_int(size as u64, false)
                .into(),
            ptr.into(),
        ],
        "lifetime_end",
    );
}

/// If this rvalue represented a moved value, mark the moved value as dead.
pub fn lifetime_end_if_moved<'ctx>(
    ctx: &BodyCreationContext<'_, 'ctx>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    variable: &Rvalue,
) {
    if let Rvalue::Move(place) = variable {
        if place.projection.is_empty() {
            // Trivially this place is now dead.
            lifetime_end(ctx, local_variable_names, &place.local);
        }
    }
}
