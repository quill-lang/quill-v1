use inkwell::{debug_info::DIType, types::BasicTypeEnum};

use crate::codegen::CodeGenContext;

#[derive(Debug, Clone, Copy)]
pub struct AnyTypeRepresentation<'ctx> {
    pub llvm_type: BasicTypeEnum<'ctx>,
    pub di_type: DIType<'ctx>,
    /// For some types, they require a higher alignment than LLVM says they do.
    /// This is particularly important for enum types, where variants may have higher alignment requirements than the base enum type itself.
    abi_alignment: u32,
}

impl<'ctx> AnyTypeRepresentation<'ctx> {
    pub fn new(
        codegen: &CodeGenContext<'ctx>,
        llvm_type: BasicTypeEnum<'ctx>,
        di_type: DIType<'ctx>,
    ) -> Self {
        let abi_alignment = codegen.target_data().get_abi_alignment(&llvm_type);
        Self {
            llvm_type,
            di_type,
            abi_alignment,
        }
    }

    pub fn new_with_alignment(
        llvm_type: BasicTypeEnum<'ctx>,
        di_type: DIType<'ctx>,
        abi_alignment: u32,
    ) -> Self {
        Self {
            llvm_type,
            di_type,
            abi_alignment,
        }
    }

    pub fn abi_alignment(&self) -> u32 {
        self.abi_alignment
    }

    pub fn store_size(&self, codegen: &CodeGenContext<'ctx>) -> u64 {
        codegen.target_data().get_store_size(&self.llvm_type)
    }
}
