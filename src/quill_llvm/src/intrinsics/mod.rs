//! This module contains handwritten LLVM IR for certain builtin functions.

use std::collections::BTreeMap;

use inkwell::{
    basic_block::BasicBlock,
    values::{BasicValue, IntValue},
    IntPredicate,
};
use quill_index::TypeParameter;
use quill_mir::mir::{ArgumentIndex, LocalVariableInfo, LocalVariableName};

use crate::codegen::BodyCreationContext;

/// Generates handwritten LLVM code for intrinsics defined internally.
pub(crate) fn create_real_func_body_intrinsic<'ctx>(
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

    match ctx.func.func.func.name.as_str() {
        "putchar" => {
            putchar(&ctx);
        }
        "getchar" => {
            getchar(&ctx);
        }
        "add_int_unchecked" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen.builder.build_int_add(lhs, rhs, "result")
            });
        }
        "sub_int_unchecked" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen.builder.build_int_sub(lhs, rhs, "result")
            });
        }
        "mul_int_unchecked" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen.builder.build_int_mul(lhs, rhs, "result")
            });
        }
        "div_int_unchecked" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen.builder.build_int_signed_div(lhs, rhs, "result")
            });
        }
        "gt_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::SGT, lhs, rhs, "result")
            });
        }
        "ge_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::SGE, lhs, rhs, "result")
            });
        }
        "lt_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::SLT, lhs, rhs, "result")
            });
        }
        "le_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::SLE, lhs, rhs, "result")
            });
        }
        "eq_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "result")
            });
        }
        "ne_int" => {
            int_binop(&ctx, |lhs, rhs| {
                ctx.codegen
                    .builder
                    .build_int_compare(IntPredicate::NE, lhs, rhs, "result")
            });
        }
        "int_to_char_intrinsic" => {
            int_unop(&ctx, |value| {
                ctx.codegen
                    .builder
                    .build_int_cast(value, ctx.codegen.context.i32_type(), "result")
            });
        }
        "char_to_int_intrinsic" => {
            int_unop(&ctx, |value| {
                ctx.codegen
                    .builder
                    .build_int_cast(value, ctx.codegen.context.i64_type(), "result")
            });
        }
        _ => {
            panic!("intrinsic {} is not defined by the compiler", ctx.func.func)
        }
    }

    block
}

fn putchar(ctx: &BodyCreationContext) {
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
    let arg0_i32 =
        ctx.codegen
            .builder
            .build_int_cast(arg0, ctx.codegen.context.i32_type(), "arg0_i32");
    ctx.codegen
        .builder
        .build_call(putchar, &[arg0_i32.into()], "call_putchar");
    ctx.codegen.builder.build_return(None);
}

fn getchar(ctx: &BodyCreationContext) {
    let getchar = ctx.codegen.module.add_function(
        "getchar",
        ctx.codegen.context.i32_type().fn_type(&[], false),
        None,
    );
    let result = ctx.codegen.builder.build_call(getchar, &[], "call_getchar");
    let result = ctx.codegen.builder.build_int_cast(
        result.try_as_basic_value().left().unwrap().into_int_value(),
        ctx.codegen.context.i64_type(),
        "result",
    );
    ctx.codegen.builder.build_return(Some(&result));
}

/// Generic unary integer operation.
fn int_unop<'ctx, F, V>(ctx: &BodyCreationContext<'_, 'ctx>, op: F)
where
    F: FnOnce(IntValue<'ctx>) -> V,
    V: BasicValue<'ctx>,
{
    let arg0 = ctx
        .codegen
        .builder
        .build_load(
            ctx.locals[&LocalVariableName::Argument(ArgumentIndex(0))],
            "arg0",
        )
        .into_int_value();
    ctx.codegen.builder.build_return(Some(&op(arg0)));
}

/// Generic binary integer operation.
fn int_binop<'ctx, F, V>(ctx: &BodyCreationContext<'_, 'ctx>, op: F)
where
    F: FnOnce(IntValue<'ctx>, IntValue<'ctx>) -> V,
    V: BasicValue<'ctx>,
{
    let arg0 = ctx
        .codegen
        .builder
        .build_load(
            ctx.locals[&LocalVariableName::Argument(ArgumentIndex(0))],
            "arg0",
        )
        .into_int_value();
    let arg1 = ctx
        .codegen
        .builder
        .build_load(
            ctx.locals[&LocalVariableName::Argument(ArgumentIndex(1))],
            "arg1",
        )
        .into_int_value();
    ctx.codegen.builder.build_return(Some(&op(arg0, arg1)));
}
