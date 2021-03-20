#[tokio::test]
async fn test_typeck() {
    use quill_common::location::SourceFileIdentifier;
    use quill_index::index_single_file;
    use quill_index::ProjectIndex;
    use quill_lexer::lex;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::path::PathBuf;

    let fs = PackageFileSystem::new(PathBuf::from("../../test_sources"));
    for &fname in &["normal_types", "higher_kinded_types", "primitive_types"] {
        let file_ident = SourceFileIdentifier {
            module: vec![].into(),
            file: fname.into(),
        };

        let lexed = lex(&fs, &file_ident).await;
        let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));
        let typeck = parsed
            .bind(|parsed| {
                index_single_file(&file_ident, &parsed).bind(|index| {
                    let mut project_index = ProjectIndex::new();
                    project_index.insert(file_ident.clone(), index);
                    quill_type_deduce::check(&file_ident, &project_index, parsed)
                })
            })
            .deny();

        let mut error_emitter = ErrorEmitter::new(&fs);
        let typeck = error_emitter.consume_diagnostic(typeck);
        error_emitter.emit_all().await;

        // If the type check fails, the test will fail.
        let typeck = typeck.unwrap();

        println!("typeck: {:#?}", typeck);
    }
}
