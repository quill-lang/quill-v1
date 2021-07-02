#[test]
fn test_typeck() {
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_index::index_single_file;
    use quill_index::ProjectIndex;
    use quill_lexer::lex;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use std::collections::HashMap;
    use std::path::PathBuf;

    let fs = PackageFileSystem::new({
        let mut map = HashMap::new();
        map.insert(
            "test_project".to_string(),
            PathBuf::from("../../test_sources"),
        );
        map
    });
    for &fname in &["main", "higher_kinded_types", "primitive_types"] {
        let file_ident = SourceFileIdentifier {
            module: vec!["test_project".into()].into(),
            file: fname.into(),
            file_type: SourceFileType::Quill,
        };

        let lexed = lex(&fs, &file_ident);
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

        let (typeck, messages) = typeck.destructure();
        let error_emitter = ErrorEmitter::new(&fs);
        for message in messages {
            error_emitter.emit(message)
        }

        // If the type check fails, the test will fail.
        let typeck = typeck.unwrap();

        println!("typeck: {:#?}", typeck);
    }
}
