use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Location, SourceFileIdentifier, SourceFileType},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_mir::ProjectMIR;
use quill_source_file::{ErrorEmitter, PackageFileSystem};
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

/// The `quillc` compiler is not intended to be used as a CLI.
/// Rather, the `quill` driver program should supply correct arguments to `quillc` in the form of JSON.
#[tokio::main]
async fn main() {
    let invocation: QuillcInvocation =
        serde_json::from_str(&std::env::args().nth(1).unwrap()).unwrap();

    let fs = PackageFileSystem::new(invocation.build_info.code_folder.clone());
    let mut error_emitter = ErrorEmitter::new(&fs);

    // No need for error handling here, the `quill.toml` file was validated by `quill` before it called this program.
    // (This is excluding the annoying case where the file changes after being parsed by `quill`, and before this program is executed.)
    let project_config = toml::from_str::<ProjectInfo>(
        std::str::from_utf8(
            &std::fs::read(invocation.build_info.code_folder.join("quill.toml")).unwrap(),
        )
        .unwrap(),
    )
    .unwrap();

    let file_ident = SourceFileIdentifier {
        module: vec![].into(),
        file: "main".into(),
        file_type: SourceFileType::Quill,
    };

    let lexed = quill_lexer::lex(&fs, &file_ident).await;
    let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &file_ident));
    let mir = parsed
        .bind(|parsed| {
            quill_index::index_single_file(&file_ident, &parsed).bind(|index| {
                let mut project_index = ProjectIndex::new();
                project_index.insert(file_ident.clone(), index);
                quill_type_deduce::check(&file_ident, &project_index, parsed)
                    .deny()
                    .bind(|typeck| quill_mir::to_mir(&project_index, typeck))
                    .deny()
                    .bind(|mir| quill_borrow_check::borrow_check(&file_ident, mir))
                    .map(|result| (result, project_index))
            })
        })
        .deny()
        .map(|(mir, index)| ProjectMIR {
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
        })
        .bind(|mir| validate(&mir).map(|_| (mir)));

    let mir = error_emitter.consume_diagnostic(mir);
    if error_emitter.emit_all().await {
        return;
    }

    let mut mir = mir.unwrap();

    quill_func_objects::convert_func_objects(&mut mir);

    quill_llvm::build(&project_config.name, &mir, invocation.build_info.clone());
    quill_link::link(
        &project_config.name,
        &invocation.deps_directory,
        invocation.build_info,
    );
}
