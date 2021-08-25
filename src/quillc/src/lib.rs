use std::{collections::BTreeMap, sync::Arc};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Location, ModuleIdentifier, SourceFileIdentifier, SourceFileType},
    name::QualifiedName,
};
use quill_mir::ProjectMIR;
use quill_source_file::{find_all_source_files, PackageFileSystem};
use quill_type::{PrimitiveType, Type};
use quillc_api::{ProjectInfo, QuillcInvocation};

/// Returns false if an error was emitted.
/// Messages are printed to stdout to communicate with the `quill` executable.
/// Messages are prefixed with one of the following tags:
/// - `status`: a status message telling `quill` the compilation stage
/// - `message`: an [ErrorMessage] to be relayed to the user, serialised into JSON
pub fn invoke(invocation: QuillcInvocation) -> bool {
    println!("status initialised");

    // No need for error handling here, the `quill.toml` file was validated by `quill` before it called this program.
    // (This is excluding the annoying case where the file changes after being parsed by `quill`, and before this program is executed.)
    let project_config = toml::from_str::<ProjectInfo>(
        std::str::from_utf8(
            &std::fs::read(invocation.build_info.code_folder.join("quill.toml")).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();

    println!("status parsed project config");

    let fs = Arc::new(PackageFileSystem::new({
        let mut map = BTreeMap::new();
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
    );

    println!("status lexing source files");

    let lexed = {
        let mut results = Vec::new();
        for file_ident in source_files.iter() {
            results
                .push(quill_lexer::lex(&fs, file_ident).map(|lexed| (file_ident.clone(), lexed)));
        }
        DiagnosticResult::sequence_unfail(results)
            .map(|results| results.into_iter().collect::<BTreeMap<_, _>>())
            .deny()
    };

    println!("status parsing source files");

    let fs2 = Arc::clone(&fs);
    let build_info = invocation.build_info.clone();
    let project_config_name = project_config.name.clone();
    let mir: DiagnosticResult<ProjectMIR> = {
        let parsed = lexed.bind(|lexed| {
            DiagnosticResult::sequence_unfail(lexed.into_iter().map(|(file, lexed)| {
                quill_parser::parse(lexed, &file).map(|parsed| (file, parsed))
            }))
            .map(|results| results.into_iter().collect::<BTreeMap<_, _>>())
            .deny()
        });

        println!("status indexing project");

        parsed
            .bind(|parsed| {
                quill_index::index_project(&parsed).bind(|index| {
                    println!("status run type deduction");
                    // Now that we have the index, run type deduction and MIR generation.
                    DiagnosticResult::sequence_unfail(parsed.into_iter().map(
                        |(file_ident, parsed)| {
                            quill_type_deduce::check(&file_ident, &index, parsed)
                                .deny()
                                .bind(|typeck| {
                                    // Output the HIR to a build file.
                                    let f = build_info.build_folder.join("ir").join(
                                        fs2.file_path(&file_ident)
                                            .strip_prefix(&build_info.code_folder)
                                            .unwrap(),
                                    );
                                    if build_info.emit_hir || build_info.emit_mir {
                                        let _ = std::fs::create_dir_all(f.parent().unwrap());
                                    }
                                    if build_info.emit_hir {
                                        std::fs::write(f.with_extension("hir"), typeck.to_string())
                                            .unwrap();
                                    }
                                    quill_mir::to_mir(&index, typeck, &file_ident).map(|mir| {
                                        if build_info.emit_mir {
                                            std::fs::write(
                                                f.with_extension("basic.mir"),
                                                mir.to_string(),
                                            )
                                            .unwrap();
                                        }
                                        mir
                                    })
                                })
                                .bind(|mir| quill_borrow_check::borrow_check(&file_ident, mir))
                                .map(|mir| {
                                    // If the `emit_mir` flag is checked, we output the MIR twice: once before borrowck and once after.
                                    if build_info.emit_mir {
                                        let f = build_info.build_folder.join("ir").join(
                                            fs2.file_path(&file_ident)
                                                .strip_prefix(&build_info.code_folder)
                                                .unwrap(),
                                        );
                                        std::fs::write(f.with_extension("mir"), mir.to_string())
                                            .unwrap();
                                    }
                                    mir
                                })
                                .map(|mir| (file_ident, mir))
                        },
                    ))
                    .map(|results| results.into_iter().collect::<BTreeMap<_, _>>())
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
            .bind(|mir| validate(&mir).map(|_| mir))
    };

    // Emit the error messages to the user.

    let (mir, messages) = mir.destructure();

    let mut emitted_error = false;
    for message in messages {
        if message.severity == Severity::Error {
            emitted_error = true;
        }
        println!("message {}", serde_json::to_string(&message).unwrap());
    }

    if emitted_error {
        false
    } else {
        let mut mir = mir.unwrap();

        println!("status converting function objects");

        quill_func_objects::convert_func_objects(&mut mir);

        // `quill_llvm` outputs its own status messages, so no need to make one here.
        quill_llvm::build(&project_config.name, mir, invocation.build_info.clone());

        println!("status linking");

        quill_link::link(
            &project_config.name,
            &invocation.zig_compiler,
            invocation.build_info,
        );

        println!("status finished");

        true
    }
}

/// Perform some basic validation that must pass in order to complete monomorphisation and code emission.
fn validate(mir: &ProjectMIR) -> DiagnosticResult<()> {
    println!("status validating mir");
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
