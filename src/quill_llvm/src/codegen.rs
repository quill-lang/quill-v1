use std::{collections::BTreeMap, path::PathBuf};

use inkwell::{
    builder::Builder,
    context::Context,
    debug_info::{DICompileUnit, DIFile, DebugInfoBuilder},
    execution_engine::ExecutionEngine,
    module::Module,
    targets::TargetData,
    types::BasicType,
    values::{BasicValue, FunctionValue, PointerValue},
};
use quill_index::ProjectIndex;
use quill_mir::mir::LocalVariableName;
use quill_monomorphise::monomorphisation::MonomorphisedCurriedFunction;
use quill_target::{TargetArchitecture, TargetTriple};

use crate::repr::LLVMRepresentations;

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
    pub reprs: &'a LLVMRepresentations<'a, 'ctx>,
    pub index: &'a ProjectIndex,
    pub func: MonomorphisedCurriedFunction,
    pub func_value: FunctionValue<'ctx>,
    pub locals: BTreeMap<LocalVariableName, PointerValue<'ctx>>,
    pub di_file: DIFile<'ctx>,
}

/// Adds definitions to the LLVM module to assert that certain libc functions
/// like `malloc` exist, and declare their types so we can use them later.
/// Some functions require some wrappers, for instance `malloc`, so for consistency
/// every libc function `f` is wrapped by some ABI-independent function called `libc::f`.
fn declare_libc<'ctx>(
    triple: TargetTriple,
    context: &'ctx Context,
    module: &Module<'ctx>,
    builder: &Builder<'ctx>,
) {
    // This line of code doesn't work for wasm32; it returns i64.
    // let size_t = context.ptr_sized_int_type(execution_engine.get_target_data(), None);
    let size_t = match triple.arch {
        TargetArchitecture::X86_64 => context.i64_type(),
        TargetArchitecture::Wasm32 => context.i32_type(),
    };

    let malloc = module.add_function(
        "malloc",
        context
            .i8_type()
            .ptr_type(inkwell::AddressSpace::Generic)
            .fn_type(&[size_t.as_basic_type_enum().into()], false),
        None,
    );
    // Wrap `malloc` so that we can always call it with an `i64` regardless of the target's pointer size.
    let malloc_wrapper = module.add_function(
        "libc::malloc",
        context
            .i8_type()
            .ptr_type(inkwell::AddressSpace::Generic)
            .fn_type(&[context.i64_type().into()], false),
        None,
    );
    {
        let block = context.append_basic_block(malloc_wrapper, "call_malloc");
        builder.position_at_end(block);
        let result = builder
            .build_call(
                malloc,
                &[builder
                    .build_int_cast(
                        malloc_wrapper.get_first_param().unwrap().into_int_value(),
                        size_t,
                        "as_ptr_sized_int",
                    )
                    .as_basic_value_enum()
                    .into()],
                "result",
            )
            .try_as_basic_value()
            .left()
            .unwrap();
        builder.build_return(Some(&result));
    }

    let free = module.add_function(
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
    let free_wrapper = module.add_function(
        "libc::free",
        context.void_type().fn_type(
            &[context
                .i8_type()
                .ptr_type(inkwell::AddressSpace::Generic)
                .into()],
            false,
        ),
        None,
    );
    {
        let block = context.append_basic_block(free_wrapper, "call_free");
        builder.position_at_end(block);
        builder.build_call(
            free,
            &[free_wrapper.get_first_param().unwrap().into()],
            "result",
        );
        builder.build_return(None);
    }
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
    pub fn new(
        triple: TargetTriple,
        context: &'ctx Context,
        module: Module<'ctx>,
        project_root: PathBuf,
    ) -> Self {
        let builder = context.create_builder();
        let execution_engine = module.create_interpreter_execution_engine().unwrap();

        declare_libc(triple, context, &module, &builder);
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
        self.module
            .get_function(&format!("libc::{}", name))
            .unwrap()
    }

    pub fn target_data(&self) -> &TargetData {
        self.execution_engine.get_target_data()
    }
}
