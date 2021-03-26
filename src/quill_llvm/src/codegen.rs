use inkwell::{builder::Builder, context::Context, module::Module, values::FunctionValue};

pub struct CodeGenContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
}

/// Creates declarations of useful functions from libc, such as `malloc` and `free`.
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

        let builder = context.create_builder();
        Self {
            context,
            module,
            builder,
        }
    }

    /// Gets a function from libc with this name.
    pub fn libc(&self, name: &str) -> FunctionValue<'ctx> {
        self.module.get_function(name).unwrap()
    }
}
