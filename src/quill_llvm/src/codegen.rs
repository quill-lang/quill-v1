use std::{collections::HashMap, path::PathBuf};

use inkwell::{
    builder::Builder,
    context::Context,
    debug_info::{DICompileUnit, DIFile, DebugInfoBuilder},
    execution_engine::ExecutionEngine,
    module::Module,
    targets::TargetData,
    values::{FunctionValue, PointerValue},
};
use quill_index::ProjectIndex;
use quill_mir::mir::LocalVariableName;

use crate::{monomorphisation::MonomorphisedFunction, repr::Representations};

pub struct CodeGenContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub execution_engine: ExecutionEngine<'ctx>,
    pub project_root: PathBuf,
    pub di_builder: DebugInfoBuilder<'ctx>,
    pub di_compile_unit: DICompileUnit<'ctx>,
}

/// Contains all the useful information when generating a function body.
pub struct BodyCreationContext<'a, 'ctx> {
    pub codegen: &'a CodeGenContext<'ctx>,
    pub reprs: &'a Representations<'a, 'ctx>,
    pub index: &'a ProjectIndex,
    pub func: MonomorphisedFunction,
    pub func_value: FunctionValue<'ctx>,
    pub locals: HashMap<LocalVariableName, PointerValue<'ctx>>,
    pub di_file: DIFile<'ctx>,
}

/// Adds definitions to the LLVM module to assert that certain libc functions
/// like `malloc` exist, and declare their types so we can use them later.
fn declare_libc<'ctx>(context: &'ctx Context, module: &Module<'ctx>) {
    module.add_function(
        "malloc",
        context
            .i8_type()
            .ptr_type(inkwell::AddressSpace::Generic)
            .fn_type(&[context.i64_type().into()], false),
        None,
    );

    module.add_function(
        "free",
        context.void_type().fn_type(
            &[context
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .into()],
            false,
        ),
        None,
    );
}

fn declare_lifetime_intrinsics<'ctx>(context: &'ctx Context, module: &Module<'ctx>) {
    module.add_function(
        "llvm.lifetime.start.p0i8",
        context.void_type().fn_type(
            &[
                context.i64_type().into(),
                context
                    .i8_type()
                    .ptr_type(inkwell::AddressSpace::Generic)
                    .into(),
            ],
            false,
        ),
        None,
    );

    module.add_function(
        "llvm.lifetime.end.p0i8",
        context.void_type().fn_type(
            &[
                context.i64_type().into(),
                context
                    .i8_type()
                    .ptr_type(inkwell::AddressSpace::Generic)
                    .into(),
            ],
            false,
        ),
        None,
    );
}

/// Creates declarations of useful functions from libc.
impl<'a, 'ctx> CodeGenContext<'ctx> {
    pub fn new(context: &'ctx Context, module: Module<'ctx>, project_root: PathBuf) -> Self {
        declare_libc(context, &module);
        declare_lifetime_intrinsics(context, &module);

        let debug_metadata_version = context.i32_type().const_int(3, false);
        module.add_basic_value_flag(
            "Debug Info Version",
            inkwell::module::FlagBehavior::Warning,
            debug_metadata_version,
        );

        // Enable CodeView emission.
        let code_view = context.i32_type().const_int(1, false);
        module.add_basic_value_flag(
            "CodeView",
            inkwell::module::FlagBehavior::Warning,
            code_view,
        );
        // Enable DWARF version 2.
        let dwarf = context.i32_type().const_int(2, false);
        module.add_basic_value_flag(
            "Dwarf Version",
            inkwell::module::FlagBehavior::Warning,
            dwarf,
        );

        let (di_builder, di_compile_unit) = module.create_debug_info_builder(
            true,
            inkwell::debug_info::DWARFSourceLanguage::C,
            "test_filename",
            "test_directory",
            "quillc",
            false,
            "", // compiler command line flags
            0,
            "",
            inkwell::debug_info::DWARFEmissionKind::Full,
            0,
            false,
            false,
            "test_sysroot",
            "test_sdk",
        );

        let builder = context.create_builder();
        let execution_engine = module.create_interpreter_execution_engine().unwrap();
        Self {
            context,
            module,
            builder,
            execution_engine,
            project_root,
            di_builder,
            di_compile_unit,
        }
    }

    /// Gets a function from libc with this name.
    pub fn libc(&self, name: &str) -> FunctionValue<'ctx> {
        self.module.get_function(name).unwrap()
    }

    pub fn target_data(&self) -> &TargetData {
        self.execution_engine.get_target_data()
    }
}
