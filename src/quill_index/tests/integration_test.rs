#[tokio::test]
async fn test_index() {
    use quill_common::location::SourceFileIdentifier;
    use quill_lexer::lex;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::path::PathBuf;

    use quill_index::index_single_file;

    let fs = PackageFileSystem::new(PathBuf::from("../../test_sources"));
    let file_ident = SourceFileIdentifier {
        module: vec![].into(),
        file: "main".into(),
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
