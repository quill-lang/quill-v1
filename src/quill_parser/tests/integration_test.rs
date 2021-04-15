#[tokio::test]
async fn test_parser() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_lexer::lex;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::path::PathBuf;

    use quill_parser::parse;

    let fs = PackageFileSystem::new(PathBuf::from("../../test_sources"));
    let file_ident = SourceFileIdentifier {
        module: vec![].into(),
        file: "main".into(),
        file_type: SourceFileType::Quill,
    };

    let lexed = lex(&fs, &file_ident).await;
    let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));

    let mut error_emitter = ErrorEmitter::new(&fs);
    let parsed = error_emitter.consume_diagnostic(parsed);
    error_emitter.emit_all().await;

    // If the parse fails, the test will fail.
    let parsed = parsed.unwrap();

    println!("parsed: {:#?}", parsed);
}
