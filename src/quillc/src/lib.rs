use std::{collections::HashMap, sync::Arc};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Location, ModuleIdentifier, SourceFileIdentifier, SourceFileType},
    name::QualifiedName,
};
use quill_mir::ProjectMIR;
use quill_source_file::{find_all_source_files, ErrorEmitter, PackageFileSystem};
use quill_type::{PrimitiveType, Type};
use quillc_api::{ProjectInfo, QuillcInvocation};

/// Perform some basic validation that must pass in order to complete monomorphisation and code emission.
fn validate(mir: &ProjectMIR) -> DiagnosticResult<()> {
    if let Some(file) = mir.files.get(&mir.entry_point.source_file) {
        if let Some(main) = file.definitions.get("main") {
            // Check that the main function has the correct signature.
            if main.arity == 0 && matches!(main.return_type, Type::Primitive(PrimitiveType::Unit)) {
                DiagnosticResult::ok(())
            } else {
                DiagnosticResult::fail(ErrorMessage::new(
                    "`main` function had incorrect function signature, expected unit type"
                        .to_string(),
                    Severity::Error,
                    Diagnostic::at(&mir.entry_point.source_file, main),
                ))
            }
        } else {
            DiagnosticResult::fail(ErrorMessage::new(
                "could not find `main` function in main source file".to_string(),
                Severity::Error,
                Diagnostic::in_file(&mir.entry_point.source_file),
            ))
        }
    } else {
        DiagnosticResult::fail(ErrorMessage::new(
            "could not find main source file".to_string(),
            Severity::Error,
            Diagnostic::in_file(&mir.entry_point.source_file),
        ))
    }
}

/// Returns an Err if an error was emitted.
pub async fn invoke(invocation: QuillcInvocation) -> Result<(), ()> {
    // No need for error handling here, the `quill.toml` file was validated by `quill` before it called this program.
    // (This is excluding the annoying case where the file changes after being parsed by `quill`, and before this program is executed.)
    let project_config = toml::from_str::<ProjectInfo>(
        std::str::from_utf8(
            &std::fs::read(invocation.build_info.code_folder.join("quill.toml")).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();

    let fs = Arc::new(PackageFileSystem::new({
        let mut map = HashMap::new();
        map.insert(
            project_config.name.clone(),
            invocation.build_info.code_folder.clone(),
        );
        map
    }));

    // Find all the source files.
    let source_files = find_all_source_files(
        ModuleIdentifier {
            segments: vec![project_config.name.clone().into()],
        },
        &invocation.build_info.code_folder,
    )
    .await;

    let lexed = {
        let mut results = Vec::new();
        for file_ident in source_files.iter() {
            results.push(
                quill_lexer::lex(&fs, file_ident)
                    .await
                    .map(|lexed| (file_ident.clone(), lexed)),
            );
        }
        DiagnosticResult::sequence_unfail(results)
            .map(|results| results.into_iter().collect::<HashMap<_, _>>())
            .deny()
    };

    let fs2 = Arc::clone(&fs);
    let build_info = invocation.build_info.clone();
    let project_config_name = project_config.name.clone();
    let mir: DiagnosticResult<ProjectMIR> = tokio::task::spawn_blocking(move || {
        let parsed = lexed.bind(|lexed| {
            DiagnosticResult::sequence_unfail(lexed.into_iter().map(|(file, lexed)| {
                quill_parser::parse(lexed, &file).map(|parsed| (file, parsed))
            }))
            .map(|results| results.into_iter().collect::<HashMap<_, _>>())
            .deny()
        });

        parsed
            .bind(|parsed| {
                quill_index::index_project(&parsed).bind(|index| {
                    // Now that we have the index, run type deduction and MIR generation.
                    DiagnosticResult::sequence_unfail(parsed.into_iter().map(
                        |(file_ident, parsed)| {
                            quill_type_deduce::check(&file_ident, &index, parsed)
                                .deny()
                                .map(|typeck| {
                                    // Output the HIR to a build file.
                                    let f = build_info.build_folder.join("ir").join(
                                        fs2.file_path(&file_ident)
                                            .strip_prefix(&build_info.code_folder)
                                            .unwrap(),
                                    );
                                    let _ = std::fs::create_dir_all(f.parent().unwrap());
                                    std::fs::write(f.with_extension("hir"), typeck.to_string())
                                        .unwrap();
                                    let mir = quill_mir::to_mir(&index, typeck, &file_ident);
                                    std::fs::write(f.with_extension("mir"), mir.to_string())
                                        .unwrap();
                                    mir
                                })
                                .bind(|mir| quill_borrow_check::borrow_check(&file_ident, mir))
                                .map(|mir| (file_ident, mir))
                        },
                    ))
                    .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                    .deny()
                    .map(|result| (result, index))
                })
            })
            .deny()
            .map(|(mir, index)| ProjectMIR {
                files: mir,
                entry_point: QualifiedName {
                    source_file: SourceFileIdentifier {
                        module: ModuleIdentifier {
                            segments: vec![project_config_name.clone().into()],
                        },
                        file: "main".to_string().into(),
                        file_type: SourceFileType::Quill,
                    },
                    name: "main".to_string(),
                    range: Location { line: 0, col: 0 }.into(),
                },
                index,
            })
            .bind(|mir| validate(&mir).map(|_| (mir)))
    })
    .await
    .unwrap();

    let mut error_emitter = ErrorEmitter::new(&fs);
    let mir = error_emitter.consume_diagnostic(mir);

    if error_emitter.emit_all().await {
        Err(())
    } else {
        tokio::task::spawn_blocking(move || {
            let mut mir = mir.unwrap();

            quill_func_objects::convert_func_objects(&mut mir);

            // println!("building");
            quill_llvm::build(&project_config.name, &mir, invocation.build_info.clone());
            // println!("linking");
            quill_link::link(
                &project_config.name,
                &invocation.zig_compiler,
                invocation.build_info,
            );
            // println!("linked");
        })
        .await
        .unwrap();

        Ok(())
    }
}
