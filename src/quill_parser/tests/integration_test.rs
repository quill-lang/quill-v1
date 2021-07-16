#[test]
fn test_parser() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_error::ErrorEmitter;
    use quill_lexer::lex;
    use quill_source_file::PackageFileSystem;
    use std::collections::HashMap;
    use std::path::PathBuf;

    use quill_parser::parse;

    let fs = PackageFileSystem::new({
        let mut map = HashMap::new();
        map.insert(
            "test_project".to_string(),
            PathBuf::from("../../test_sources"),
        );
        map
    });
    let file_ident = SourceFileIdentifier {
        module: vec!["test_project".into()].into(),
        file: "main".into(),
        file_type: SourceFileType::Quill,
    };

    let lexed = lex(&fs, &file_ident);
    let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));

    let (parsed, messages) = parsed.destructure();
    let error_emitter = ErrorEmitter::new(&fs);
    for message in messages {
        error_emitter.emit(message)
    }

    // If the parse fails, the test will fail.
    let parsed = parsed.unwrap();

    println!("parsed: {:#?}", parsed);
}
