use inkwell::debug_info::DIFile;
use quill_common::location::SourceFileIdentifier;

use crate::codegen::CodeGenContext;

pub fn source_file_debug_info<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    source_file: &SourceFileIdentifier,
) -> DIFile<'ctx> {
    codegen.di_builder.create_file(
        &format!(
            "{}.{}",
            source_file.file.0,
            source_file.file_type.file_extension()
        ),
        &dunce::simplified(
            &source_file
                .module
                .segments
                .iter()
                .skip(1)
                .map(|seg| seg.0.as_str())
                .fold(codegen.project_root.clone(), |acc, segment| {
                    acc.join(segment)
                }),
        )
        .to_string_lossy(),
    )
}
