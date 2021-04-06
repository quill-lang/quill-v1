use std::{collections::HashMap, path::Path};

use quill_common::{
    location::{Location, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::ProjectIndex;
use quill_mir::ProjectMIR;
use quill_source_file::{ErrorEmitter, PackageFileSystem};
use quillc_api::QuillcInvocation;

/// The `quillc` compiler is not intended to be used as a CLI.
/// Rather, the `quill` driver program should supply correct arguments to `quillc` in the form of JSON.
#[tokio::main]
async fn main() {
    let invocation: QuillcInvocation =
        serde_json::from_str(&std::env::args().nth(1).unwrap()).unwrap();

    let fs = PackageFileSystem::new(invocation.build_info.code_folder.clone());

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
    };

    quill_func_objects::convert_func_objects(&mut proj);

    quill_llvm::build("main", &proj, &index, invocation.build_info.clone());
    quill_link::link(
        &Path::new("../compiler-deps").canonicalize().unwrap(),
        invocation.build_info,
    );
}
