#[test]
fn test_borrowck() {
    use quill_borrow_check::borrow_check;
    use quill_common::location::SourceFileIdentifier;
    use quill_common::location::SourceFileType;
    use quill_error::ErrorEmitter;
    use quill_index::index_single_file;
    use quill_lexer::lex;
    use quill_mir::to_mir;
    use quill_mir::SourceFileMIR;
    use quill_parser::parse;
    use quill_source_file::PackageFileSystem;
    use quill_type_deduce::check;
    use std::collections::BTreeMap;
    use std::path::PathBuf;

    let fs = PackageFileSystem::new({
        let mut map = BTreeMap::new();
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
        let mir = parsed
            .bind(|parsed| {
                index_single_file(&file_ident, &parsed).bind(|project_index| {
                    check(&file_ident, &project_index, parsed)
                        .deny()
                        .bind(|typeck| to_mir(&project_index, typeck, &file_ident))
                        .deny()
                        .bind(|mir| borrow_check(&file_ident, mir))
                })
            })
            .deny();

        let (mir, messages) = mir.destructure();
        let error_emitter = ErrorEmitter::new(&fs);
        for message in messages {
            error_emitter.emit(message)
        }

        // If the borrow check fails, the test will fail.
        let mir: SourceFileMIR = mir.unwrap();

        for (def_name, def) in mir.definitions {
            println!("def: {}", def_name);
            println!("{}", def);
        }
    }
}
