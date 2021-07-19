#[test]
fn test_lexer() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_error::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::collections::BTreeMap;
    use std::path::PathBuf;

    use quill_lexer::lex;

    let fs = PackageFileSystem::new({
        let mut map = BTreeMap::new();
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
    );

    let (lexed, messages) = lexed.destructure();
    let error_emitter = ErrorEmitter::new(&fs);
    for message in messages {
        error_emitter.emit(message)
    }

    // If the lex fails, the test will fail.
    let lexed = lexed.unwrap();

    println!("lexed: {:#?}", lexed);
}
