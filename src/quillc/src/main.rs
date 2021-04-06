use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, Severity},
    location::{Location, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_mir::ProjectMIR;
use quill_source_file::{ErrorEmitter, PackageFileSystem};
use quillc_api::{ProjectInfo, QuillcInvocation};

async fn exit(mut emitter: ErrorEmitter<'_>, error_message: ErrorMessage) -> ! {
    emitter.process(vec![error_message]);
    emitter.emit_all().await;
    std::process::exit(1)
}

/// The `quillc` compiler is not intended to be used as a CLI.
/// Rather, the `quill` driver program should supply correct arguments to `quillc` in the form of JSON.
#[tokio::main]
async fn main() {
    let invocation: QuillcInvocation =
        serde_json::from_str(&std::env::args().nth(1).unwrap()).unwrap();

    let fs = PackageFileSystem::new(invocation.build_info.code_folder.clone());
    let mut error_emitter = ErrorEmitter::new(&fs);

    let project_config = if let Ok(project_config_str) =
        std::fs::read(invocation.build_info.code_folder.join("quill.toml"))
    {
        match std::str::from_utf8(&project_config_str) {
            Ok(project_config_str) => match toml::from_str::<ProjectInfo>(project_config_str) {
                Ok(toml) => toml,
                Err(err) => {
                    let (line, col) = err.line_col().unwrap_or((0, 0));
                    exit(
                        error_emitter,
                        ErrorMessage::new(
                            format!("'quill.toml' contained an error: {}", err),
                            Severity::Error,
                            Diagnostic::at_location(
                                &SourceFileIdentifier {
                                    module: vec![].into(),
                                    file: "quill.toml".into(),
                                },
                                Location {
                                    line: line as u32,
                                    col: col as u32,
                                },
                            ),
                        ),
                    )
                    .await
                }
            },
            Err(err) => {
                let (valid, after_valid) = project_config_str.split_at(err.valid_up_to());
                let safe_str = unsafe { std::str::from_utf8_unchecked(valid) };
                let safe_str_chars = safe_str.chars().collect::<Vec<_>>();
                let safe_str_slice: String = safe_str_chars
                    [std::cmp::max(20, safe_str_chars.len()) - 20..]
                    .iter()
                    .collect();
                exit(
                    error_emitter,
                    ErrorMessage::new(
                        format!(
                        "'quill.toml' contained invalid UTF-8 after '...{}', bytes were {:02X?}",
                        safe_str_slice,
                        &after_valid[..std::cmp::min(10, after_valid.len())]
                    ),
                        Severity::Error,
                        Diagnostic::in_file(&SourceFileIdentifier {
                            module: vec![].into(),
                            file: "quill.toml".into(),
                        }),
                    ),
                )
                .await
            }
        }
    } else {
        exit(
            error_emitter,
            ErrorMessage::new(
                "'quill.toml' file could not be found".to_string(),
                Severity::Error,
                Diagnostic::in_file(&SourceFileIdentifier {
                    module: vec![].into(),
                    file: "quill.toml".into(),
                }),
            ),
        )
        .await
    };

    let file_ident = SourceFileIdentifier {
        module: vec![].into(),
        file: "main".into(),
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
        .deny();

    let mir = error_emitter.consume_diagnostic(mir);
    error_emitter.emit_all().await;

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
    };

    quill_func_objects::convert_func_objects(&mut proj);

    quill_llvm::build(
        &project_config.name,
        &proj,
        &index,
        invocation.build_info.clone(),
    );
    quill_link::link(
        &project_config.name,
        &invocation.deps_directory,
        invocation.build_info,
    );
}
