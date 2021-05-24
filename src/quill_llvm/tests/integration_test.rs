#[tokio::test]
async fn test_llvm() {
    use std::collections::HashMap;
    use std::path::Path;

    use quill_borrow_check::borrow_check;
    use quill_common::location::SourceFileIdentifier;
    use quill_common::{
        location::{Location, SourceFileType},
        name::QualifiedName,
    };
    use quill_func_objects::convert_func_objects;
    use quill_index::index_single_file;
    use quill_index::ProjectIndex;
    use quill_lexer::lex;
    use quill_mir::to_mir;
    use quill_mir::ProjectMIR;
    use quill_parser::parse;
    use quill_source_file::ErrorEmitter;
    use quill_source_file::PackageFileSystem;
    use quill_target::{
        BuildInfo, TargetArchitecture, TargetEnvironment, TargetOS, TargetTriple, TargetVendor,
    };
    use quill_type_deduce::check;
    use std::path::PathBuf;

    let fs = PackageFileSystem::new({
        let mut map = HashMap::new();
        map.insert(
            "test_project".to_string(),
            PathBuf::from("../../test_sources"),
        );
        map
    });
    for &fname in &["main", "primitive_types"] {
        let file_ident = SourceFileIdentifier {
            module: vec!["test_project".into()].into(),
            file: fname.into(),
            file_type: SourceFileType::Quill,
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
                        .map(|typeck| to_mir(&project_index, typeck, &file_ident))
                        .bind(|mir| borrow_check(&file_ident, mir))
                        .map(|result| (result, project_index))
                })
            })
            .deny();

        let mut error_emitter = ErrorEmitter::new(&fs);
        let mir = error_emitter.consume_diagnostic(mir);
        error_emitter.emit_all().await;

        // If the borrow check fails, the test will fail.
        let (mir, index) = mir.unwrap();
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
            index,
        };

        convert_func_objects(&mut proj);

        let target_triple = TargetTriple {
            arch: TargetArchitecture::X86_64,
            vendor: TargetVendor::Unknown,
            os: TargetOS::Linux,
            env: Some(TargetEnvironment::Gnu),
        };

        let code_folder = Path::new("../../test_sources").into();
        let build_folder = Path::new("../../test_sources/build/test_build")
            .join(fname)
            .join(target_triple.to_string());

        std::fs::create_dir_all(&build_folder).unwrap();
        let build_folder = build_folder.canonicalize().unwrap();

        let build_info = BuildInfo {
            target_triple,
            code_folder,
            build_folder,
        };

        quill_llvm::build(fname, &proj, build_info.clone());
        quill_link::link("out", &PathBuf::from("zig"), build_info);
    }
}
