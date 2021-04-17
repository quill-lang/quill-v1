use std::{
    collections::HashMap,
    path::{Component, Path, PathBuf},
    sync::Arc,
};

use lspower::jsonrpc;
use lspower::lsp::*;
use lspower::{Client, LanguageServer, LspService, Server};
use multimap::MultiMap;
use quill_common::diagnostic::DiagnosticResult;
use quill_common::name::QualifiedName;
use quill_common::{
    diagnostic::{ErrorMessage, Severity},
    location::{ModuleIdentifier, SourceFileIdentifier, SourceFileType},
};
use quill_mir::ProjectMIR;
use quill_source_file::PackageFileSystem;
use quillc_api::ProjectInfo;
use tokio::sync::RwLock;
use tracing::{info, trace, Level};

/// Takes a relativised path and converts it to a source file identifier.
fn path_to_file(root_module: String, path: &Path) -> SourceFileIdentifier {
    let map = |component| match component {
        Component::Normal(component) => component.to_string_lossy().to_string(),
        _ => unreachable!(),
    };

    let ext = path.extension();
    let path = path.with_extension("");

    let mut components = path.components().collect::<Vec<_>>();
    let file = components.pop().unwrap();
    SourceFileIdentifier {
        module: ModuleIdentifier {
            segments: std::iter::once(root_module)
                .chain(components.into_iter().map(map))
                .map(|str| str.into())
                .collect(),
        },
        file: map(file).into(),
        file_type: if let Some(ext) = ext {
            let ext = ext.to_string_lossy().to_string();
            match ext.as_str() {
                "ql" => SourceFileType::Quill,
                "toml" => SourceFileType::Toml,
                _ => unreachable!("ext was {}", ext),
            }
        } else {
            unreachable!()
        },
    }
}

fn file_to_url(project_roots: &HashMap<String, PathBuf>, file: SourceFileIdentifier) -> Url {
    let mut iter = file
        .module
        .segments
        .into_iter()
        .chain(std::iter::once(file.file));
    let project = iter.next().unwrap().0;
    let project_root = project_roots[&project].clone();
    let segments = iter.map(|segment| segment.0);
    Url::from_file_path(
        segments
            .fold(project_root, |dir, segment| dir.join(segment))
            .with_extension(file.file_type.file_extension()),
    )
    .unwrap()
}

fn into_diagnostic(project_roots: &HashMap<String, PathBuf>, message: ErrorMessage) -> Diagnostic {
    let related_information = if message.help.is_empty() {
        None
    } else {
        Some(
            message
                .help
                .into_iter()
                .map(|help| DiagnosticRelatedInformation {
                    location: Location {
                        uri: file_to_url(project_roots, help.diagnostic.source_file),
                        range: help.diagnostic.range.map_or(
                            Range {
                                start: Position {
                                    line: 0,
                                    character: 0,
                                },
                                end: Position {
                                    line: 0,
                                    character: 0,
                                },
                            },
                            |range| Range {
                                start: Position {
                                    line: range.start.line,
                                    character: range.start.col,
                                },
                                end: Position {
                                    line: range.end.line,
                                    character: range.end.col,
                                },
                            },
                        ),
                    },
                    message: help.message,
                })
                .collect(),
        )
    };

    Diagnostic {
        range: message.diagnostic.range.map_or(
            Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 0,
                },
            },
            |range| Range {
                start: Position {
                    line: range.start.line,
                    character: range.start.col,
                },
                end: Position {
                    line: range.end.line,
                    character: range.end.col,
                },
            },
        ),
        severity: Some(match message.severity {
            Severity::Error => DiagnosticSeverity::Error,
            Severity::Warning => DiagnosticSeverity::Warning,
        }),
        code: None,
        code_description: None,
        source: Some("quill_lsp".to_string()),
        message: message.message,
        related_information,
        tags: None,
        data: None,
    }
}

struct Backend {
    client: Client,
    /// A new file system is created for every potential root.
    root_file_systems: Arc<RwLock<RootFileSystems>>,
    /// Maps project roots to the files in which diagnostics were emitted.
    /// This allows us to clear the diagnostics before emitting more.
    emitted_diagnostics_to: Arc<RwLock<HashMap<PathBuf, Vec<SourceFileIdentifier>>>>,
}

struct ProjectRoot {
    dir: PathBuf,
    project_name: String,
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            root_file_systems: Arc::new(RwLock::new(RootFileSystems::default())),
            emitted_diagnostics_to: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Check whether the given URI is inside a Quill project.
    /// This function returns the project root folder, which can be used as a key
    /// in RootFileSystems, along with the identifier of the source file relative to
    /// the project root.
    ///
    /// In particular, this checks parent URIs until a `quill.toml` file is found.
    /// If one is found, then that directory is added to `RootFileSystems` as a file
    /// system root.
    pub async fn get_project_root(&self, url: Url) -> Option<(SourceFileIdentifier, ProjectRoot)> {
        assert!(url.scheme() == "file");
        let path = url.to_file_path().unwrap();

        // First, check if we've already loaded this project folder.
        {
            let read = self.root_file_systems.read().await;
            for (k, (root_module, _)) in &read.file_systems {
                if let Ok(relative) = path.strip_prefix(k) {
                    return Some((
                        path_to_file(root_module.clone(), relative),
                        ProjectRoot {
                            dir: k.clone(),
                            project_name: root_module.clone(),
                        },
                    ));
                }
            }
        }

        let mut new_path = path.clone();
        loop {
            if let Ok(file_bytes) = tokio::fs::read(new_path.join("quill.toml")).await {
                if let Ok(file_str) = std::str::from_utf8(&file_bytes) {
                    if let Ok(file_toml) = toml::from_str::<ProjectInfo>(file_str) {
                        let fs = PackageFileSystem::new({
                            let mut map = HashMap::new();
                            map.insert(file_toml.name.clone(), new_path.clone());
                            map
                        });
                        info!(
                            "found quill project '{}' at {}",
                            file_toml.name,
                            new_path.to_str().unwrap()
                        );
                        self.root_file_systems
                            .write()
                            .await
                            .file_systems
                            .insert(new_path.clone(), (file_toml.name.clone(), fs));
                        return Some((
                            path_to_file(
                                file_toml.name.clone(),
                                path.strip_prefix(&new_path).unwrap(),
                            ),
                            ProjectRoot {
                                dir: new_path,
                                project_name: file_toml.name,
                            },
                        ));
                    }
                }
            }

            if !new_path.pop() {
                return None;
            }
        }
    }

    async fn emit_project_diagnostics(
        &self,
        project_root: PathBuf,
        fs: &PackageFileSystem,
        messages: impl IntoIterator<Item = ErrorMessage>,
    ) {
        let diagnostics_by_file = messages
            .into_iter()
            .map(|message| (message.diagnostic.source_file.clone(), message))
            .collect::<MultiMap<_, _>>();

        let mut emitted = self.emitted_diagnostics_to.write().await;
        let emitted = emitted.entry(project_root).or_default();

        for file in emitted.iter() {
            self.client
                .publish_diagnostics(
                    file_to_url(&fs.project_directories, file.clone()),
                    vec![],
                    None,
                )
                .await;
        }

        emitted.clear();

        for (file, diagnostics) in diagnostics_by_file {
            emitted.push(file.clone());
            let diags = diagnostics
                .into_iter()
                .map(|message| into_diagnostic(&fs.project_directories, message))
                .collect();

            self.client
                .publish_diagnostics(file_to_url(&fs.project_directories, file), diags, None)
                .await;
        }
    }
}

/// Creates a PackageFileSystem for every Quill project we find.
#[derive(Default)]
struct RootFileSystems {
    /// Maps workspace roots to package file systems and the name of the package at that root.
    pub file_systems: HashMap<PathBuf, (String, PackageFileSystem)>,
}

#[lspower::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> jsonrpc::Result<InitializeResult> {
        let capabilities = ServerCapabilities {
            text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::Full)),
            ..Default::default()
        };

        let server_info = ServerInfo {
            name: "quill-lsp".to_string(),
            version: None,
        };

        Ok(InitializeResult {
            capabilities,
            server_info: Some(server_info),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        info!("server initialized!");
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        info!("opened file");
        self.did_change(DidChangeTextDocumentParams {
            text_document: VersionedTextDocumentIdentifier {
                uri: params.text_document.uri,
                version: params.text_document.version,
            },
            content_changes: vec![TextDocumentContentChangeEvent {
                text: params.text_document.text,
                range: None,
                range_length: None,
            }],
        })
        .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Since we're using full text document synchronisation, we can just get the first change and that will be the whole document.
        if let Some((identifier, project_root)) = self
            .get_project_root(params.text_document.uri.clone())
            .await
        {
            trace!(
                "file {} in {} changed",
                identifier,
                project_root.dir.to_string_lossy(),
            );
            let contents = params.content_changes[0].text.clone();
            let guard = self.root_file_systems.read().await;
            let (_, fs) = &guard.file_systems[&project_root.dir];
            fs.overwrite_source_file(identifier.clone(), contents).await;

            // Parse the file and emit diagnostics.
            let lexed = quill_lexer::lex(fs, &identifier).await;
            let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &identifier));
            let (_, messages) = parsed.destructure();

            let diags = messages
                .into_iter()
                .map(|message| into_diagnostic(&fs.project_directories, message))
                .collect();

            self.client
                .publish_diagnostics(params.text_document.uri, diags, None)
                .await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        info!("closed file");
        // Remove the cached entry from the file system so that it reads the truth
        // of the file from disk when it next needs to.
        if let Some((identifier, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            self.root_file_systems.read().await.file_systems[&project_root.dir]
                .1
                .remove_cache(&identifier)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        info!("saved file");

        if let Some((_file_ident, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            // Create more detailed diagnostics by running the full Quill compiler
            // (at least, up to the MIR step) on this file's project root.
            let guard = self.root_file_systems.read().await;
            let fs = &guard.file_systems[&project_root.dir].1;

            // Find all the source files.
            let source_files = quill_source_file::find_all_source_files(
                ModuleIdentifier {
                    segments: vec![project_root.project_name.clone().into()],
                },
                &project_root.dir,
            )
            .await;

            let lexed = {
                let mut results = Vec::new();
                for file_ident in source_files.iter() {
                    results.push(
                        quill_lexer::lex(&fs, &file_ident)
                            .await
                            .map(|lexed| (file_ident.clone(), lexed)),
                    );
                }
                DiagnosticResult::sequence_unfail(results)
                    .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                    .deny()
            };

            let parsed = lexed.bind(|lexed| {
                DiagnosticResult::sequence_unfail(lexed.into_iter().map(|(file, lexed)| {
                    quill_parser::parse(lexed, &file).map(|parsed| (file, parsed))
                }))
                .map(|results| results.into_iter().collect::<HashMap<_, _>>())
                .deny()
            });

            let mir = parsed
                .bind(|parsed| {
                    quill_index::index_project(&parsed).bind(|index| {
                        // Now that we have the index, run type deduction and MIR generation.
                        DiagnosticResult::sequence_unfail(parsed.into_iter().map(
                            |(file_ident, parsed)| {
                                quill_type_deduce::check(&file_ident, &index, parsed)
                                    .deny()
                                    .bind(|typeck| quill_mir::to_mir(&index, typeck))
                                    .deny()
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
                                segments: vec![project_root.project_name.clone().into()],
                            },
                            file: "main".to_string().into(),
                            file_type: SourceFileType::Quill,
                        },
                        name: "main".to_string(),
                        range: quill_common::location::Location { line: 0, col: 0 }.into(),
                    },
                    index,
                });

            let (_, messages) = mir.destructure();

            info!(
                "compiled {:?} with {} messages",
                source_files,
                messages.len()
            );

            self.emit_project_diagnostics(project_root.dir, fs, messages)
                .await;
        }
    }

    async fn shutdown(&self) -> jsonrpc::Result<()> {
        Ok(())
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    tracing_subscriber::fmt()
        .with_ansi(false)
        .with_writer(std::io::stderr)
        .with_max_level(Level::INFO)
        .with_env_filter("quill_lsp=trace,lspower=trace")
        .init();

    let (service, messages) = LspService::new(Backend::new);
    Server::new(stdin, stdout)
        .interleave(messages)
        .serve(service)
        .await;
}
