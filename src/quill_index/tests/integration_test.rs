#[test]
fn test_index() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_lexer::lex;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::collections::HashMap;
    use std::path::PathBuf;

    use quill_index::index_single_file;

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
    let index = parsed.bind(|parsed| index_single_file(&file_ident, &parsed));

    let (index, messages) = index.destructure();
    let error_emitter = ErrorEmitter::new(&fs);
    for message in messages {
        error_emitter.emit(message)
    }

    // If the index fails, the test will fail.
    let index = index.unwrap();

    println!("index: {:#?}", index);
}
