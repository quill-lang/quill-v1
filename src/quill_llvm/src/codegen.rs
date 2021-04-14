use inkwell::{
    builder::Builder, context::Context, execution_engine::ExecutionEngine, module::Module,
    targets::TargetData, values::FunctionValue,
};

pub struct CodeGenContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub execution_engine: ExecutionEngine<'ctx>,
}

/// Creates declarations of useful functions from libc.
impl<'a, 'ctx> CodeGenContext<'ctx> {
    pub fn new(context: &'ctx Context, module: Module<'ctx>) -> Self {
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

        let builder = context.create_builder();
        let execution_engine = module.create_interpreter_execution_engine().unwrap();
        Self {
            context,
            module,
            builder,
            execution_engine,
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
