#[tokio::test]
async fn test_lexer() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::collections::HashMap;
    use std::path::PathBuf;

    use quill_lexer::lex;

    let fs = PackageFileSystem::new({
        let mut map = HashMap::new();
        map.insert(
            "test_project".to_string(),
            PathBuf::from("../../test_sources"),
        );
        map
    });
    let lexed = lex(
        &fs,
        &SourceFileIdentifier {
            module: vec!["test_project".into()].into(),
            file: "main".into(),
            file_type: SourceFileType::Quill,
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
