pub(crate) mod index_resolve;
pub(crate) mod type_check;
pub(crate) mod type_deduce;
pub(crate) mod type_resolve;

mod test {
    #[tokio::test]
    async fn test_parser() {
        use quill_common::location::SourceFileIdentifier;
        use quill_index::index_single_file;
        use quill_index::ProjectIndex;
        use quill_lexer::lex;
        use quill_parser::parse;
        use quill_source_file::ErrorEmitter;
        use quill_source_file::PackageFileSystem;
        use std::path::PathBuf;

        let fs = PackageFileSystem::new(PathBuf::from("test"));
        let file_ident = SourceFileIdentifier {
            module: vec![].into(),
            file: "file".into(),
        };

        let lexed = lex(&fs, &file_ident).await;
        let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));
        let typeck = parsed.bind(|parsed| {
            index_single_file(&file_ident, &parsed).bind(|index| {
                let mut project_index = ProjectIndex::new();
                project_index.insert(file_ident.clone(), index);
                crate::type_check::check(&file_ident, &project_index, parsed)
            })
        });

        let mut error_emitter = ErrorEmitter::new(&fs);
        let typeck = error_emitter.consume_diagnostic(typeck);
        error_emitter.emit_all().await;

        // If the type check fails, the test will fail.
        let typeck = typeck.unwrap();

        println!("typeck: {:#?}", typeck);
    }
}
