mod main_index;
mod type_index;
pub(crate) mod type_resolve;
pub use main_index::*;

use quill_common::{diagnostic::DiagnosticResult, location::SourceFileIdentifier};
use quill_parser::FileP;
use type_index::{compute_types, ProjectTypesC};

pub fn index_single_file(
    file_ident: &SourceFileIdentifier,
    parsed: &FileP,
) -> DiagnosticResult<FileIndex> {
    compute_types(&file_ident, &parsed).bind(|cache| {
        let mut project_types = ProjectTypesC::new();
        project_types.insert(file_ident.clone(), cache);
        index(&file_ident, &parsed, &project_types)
    })
}

mod test {
    #[tokio::test]
    async fn test_index() {
        use quill_common::location::SourceFileIdentifier;
        use quill_lexer::lex;
        use quill_parser::parse;
        use quill_source_file::ErrorEmitter;
        use quill_source_file::PackageFileSystem;
        use std::path::PathBuf;

        use crate::index_single_file;

        let fs = PackageFileSystem::new(PathBuf::from("test"));
        let file_ident = SourceFileIdentifier {
            module: vec![].into(),
            file: "file".into(),
        };

        let lexed = lex(&fs, &file_ident).await;
        let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));
        let index = parsed.bind(|parsed| index_single_file(&file_ident, &parsed));

        let mut error_emitter = ErrorEmitter::new(&fs);
        let index = error_emitter.consume_diagnostic(index);
        error_emitter.emit_all().await;

        // If the index fails, the test will fail.
        let index = index.unwrap();

        println!("index: {:#?}", index);
    }
}
