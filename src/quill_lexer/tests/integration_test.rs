#[tokio::test]
async fn test_lexer() {
    use quill_common::location::SourceFileIdentifier;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::path::PathBuf;

    use quill_lexer::lex;

    let fs = PackageFileSystem::new(PathBuf::from("../../test_sources"));
    let lexed = lex(
        &fs,
        &SourceFileIdentifier {
            module: vec![].into(),
            file: "main".into(),
        },
    )
    .await;

    let mut error_emitter = ErrorEmitter::new(&fs);
    let lexed = error_emitter.consume_diagnostic(lexed);
    error_emitter.emit_all().await;

    // If the lex fails, the test will fail.
    let lexed = lexed.unwrap();

    println!("lexed: {:#?}", lexed);
}
