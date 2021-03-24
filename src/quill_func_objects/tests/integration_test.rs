use std::collections::HashMap;

use quill_common::{location::Location, name::QualifiedName};
use quill_mir::{ProjectMIR, SourceFileMIR};

#[tokio::test]
async fn test_convert_func_objects() {
    use quill_borrow_check::borrow_check;
    use quill_common::location::SourceFileIdentifier;
    use quill_func_objects::convert_func_objects;
    use quill_index::index_single_file;
    use quill_index::ProjectIndex;
    use quill_lexer::lex;
    use quill_mir::to_mir;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use quill_type_deduce::check;
    use std::path::PathBuf;

    let fs = PackageFileSystem::new(PathBuf::from("../../test_sources"));
    for &fname in &["normal_types", "higher_kinded_types", "primitive_types"] {
        let file_ident = SourceFileIdentifier {
            module: vec![].into(),
            file: fname.into(),
        };

        let lexed = lex(&fs, &file_ident).await;
        let parsed = lexed.bind(|lexed| parse(lexed, &file_ident));
        let mir = parsed
            .bind(|parsed| {
                index_single_file(&file_ident, &parsed).bind(|index| {
                    let mut project_index = ProjectIndex::new();
                    project_index.insert(file_ident.clone(), index);
                    check(&file_ident, &project_index, parsed)
                        .deny()
                        .bind(|typeck| to_mir(&project_index, typeck))
                        .deny()
                        .bind(|mir| borrow_check(&file_ident, mir))
                })
            })
            .deny();

        let mut error_emitter = ErrorEmitter::new(&fs);
        let mir = error_emitter.consume_diagnostic(mir);
        error_emitter.emit_all().await;

        // If the conversion fails, the test will fail.
        let mir: SourceFileMIR = mir.unwrap();
        let mut proj = ProjectMIR {
            files: {
                let mut map = HashMap::new();
                map.insert(file_ident.clone(), mir);
                map
            },
            entry_point: QualifiedName {
                source_file: file_ident,
                name: "main".to_string(),
                range: Location { line: 0, col: 0 }.into(),
            },
        };

        convert_func_objects(&mut proj);

        for (file_id, file) in proj.files {
            println!("-----\n{}\n-----", file_id);
            for (def_name, def) in file.definitions {
                println!("def: {}", def_name);
                println!("{}", def);
            }
        }
    }
}
