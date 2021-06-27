use inkwell::types::StructType;

use crate::codegen::CodeGenContext;

#[derive(Debug, Clone)]
pub struct LLVMStructRepresentation<'ctx> {
    pub ty: StructType<'ctx>,
    /// For some types, they require a higher alignment than LLVM says they do.
    /// This is particularly important for enum types, where variants may have higher alignment requirements than the base enum type itself.
    pub abi_alignment: u32,
}

impl<'ctx> LLVMStructRepresentation<'ctx> {
    pub fn new(codegen: &CodeGenContext<'ctx>, ty: StructType<'ctx>) -> Self {
        let abi_alignment = codegen.target_data().get_abi_alignment(&ty);
        Self { ty, abi_alignment }
    }

    pub fn new_with_alignment(ty: StructType<'ctx>, abi_alignment: u32) -> Self {
        Self { ty, abi_alignment }
    }

    pub fn store_size(&self, codegen: &CodeGenContext<'ctx>) -> u64 {
        codegen.target_data().get_store_size(&self.ty)
    }
}
