use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::Arc,
};

use lspower::jsonrpc;
use lspower::lsp::*;
use lspower::{Client, LanguageServer, LspService, Server};
use multimap::MultiMap;
use quill_common::{
    diagnostic::{ErrorMessage, Severity},
    location::SourceFileIdentifier,
};
use quill_source_file::PackageFileSystem;
use quillc_api::ProjectInfo;
use tokio::sync::RwLock;
use tracing::{info, trace, Level};

/// Takes a relativised path and converts it to a source file identifier.
fn path_to_file(_root_module: String, _path: &Path) -> SourceFileIdentifier {
    unimplemented!()
}

fn file_to_url(_project_root: &Path, _file: SourceFileIdentifier) -> Url {
    unimplemented!()
    //Url::from_file_path(project_root.join(file_to_path(file))).unwrap()
}

fn into_diagnostic(project_root: &Path, message: ErrorMessage) -> Diagnostic {
    let related_information = if message.help.is_empty() {
        None
    } else {
        Some(
            message
                .help
                .into_iter()
                .map(|help| DiagnosticRelatedInformation {
                    location: Location {
                        uri: file_to_url(project_root, help.diagnostic.source_file),
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
}

impl Backend {
    pub fn new(client: Client) -> Self {
        Self {
            client,
            root_file_systems: Arc::new(RwLock::new(RootFileSystems::default())),
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
    pub async fn get_project_root(&self, url: Url) -> Option<(SourceFileIdentifier, PathBuf)> {
        assert!(url.scheme() == "file");
        let path = url.to_file_path().unwrap();

        // First, check if we've already loaded this project folder.
        {
            let read = self.root_file_systems.read().await;
            for (k, (root_module, _)) in &read.file_systems {
                if let Ok(relative) = path.strip_prefix(k) {
                    return Some((path_to_file(root_module.clone(), relative), k.clone()));
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
                            path_to_file(file_toml.name, path.strip_prefix(&new_path).unwrap()),
                            new_path,
                        ));
                    }
                }
            }

            if !new_path.pop() {
                return None;
            }
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
                project_root.to_string_lossy(),
            );
            let contents = params.content_changes[0].text.clone();
            let guard = self.root_file_systems.read().await;
            let (_, fs) = &guard.file_systems[&project_root];
            fs.overwrite_source_file(identifier.clone(), contents).await;

            // Parse the file and emit diagnostics.
            let lexed = quill_lexer::lex(fs, &identifier).await;
            let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &identifier));
            let (_, messages) = parsed.destructure();

            let diags = messages
                .into_iter()
                .map(|message| into_diagnostic(&project_root, message))
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
            self.root_file_systems.read().await.file_systems[&project_root]
                .1
                .remove_cache(&identifier)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        info!("saved file");

        if let Some((file_ident, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            // Create more detailed diagnostics by running the full Quill compiler
            // (at least, up to the MIR step) on this file's project root.
            let guard = self.root_file_systems.read().await;
            let fs = &guard.file_systems[&project_root].1;
            let lexed = quill_lexer::lex(&fs, &file_ident).await;
            let parsed = lexed.bind(|lexed| quill_parser::parse(lexed, &file_ident));
            let mir = parsed
                .bind(|parsed| {
                    quill_index::index_single_file(&file_ident, &parsed).bind(|index| {
                        let mut project_index = quill_index::ProjectIndex::new();
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

            let (_, messages) = mir.destructure();

            let diagnostics_by_file = messages
                .into_iter()
                .map(|message| (message.diagnostic.source_file.clone(), message))
                .collect::<MultiMap<_, _>>();

            for (file, diagnostics) in diagnostics_by_file {
                let diags = diagnostics
                    .into_iter()
                    .map(|message| into_diagnostic(&project_root, message))
                    .collect();

                self.client
                    .publish_diagnostics(file_to_url(&project_root, file), diags, None)
                    .await;
            }
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
