use std::{collections::HashMap, path::PathBuf, sync::Arc};

use lspower::jsonrpc;
use lspower::lsp::*;
use lspower::{Client, LanguageServer, LspService, Server};
use quill_source_file::PackageFileSystem;
use quillc_api::ProjectInfo;
use tokio::sync::RwLock;
use tracing::{info, trace, Level};

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
    pub async fn get_project_root(
        &self,
        url: Url,
    ) -> Option<(quill_common::location::SourceFileIdentifier, PathBuf)> {
        assert!(url.scheme() == "file");
        let path = url.to_file_path().unwrap();

        // First, check if we've already loaded this project folder.
        {
            let read = self.root_file_systems.read().await;
            for k in read.file_systems.keys() {
                if let Ok(relative) = path.strip_prefix(k) {
                    return Some((relative.into(), k.clone()));
                }
            }
        }

        let mut new_path = path.clone();
        loop {
            if let Ok(file_bytes) = tokio::fs::read(new_path.join("quill.toml")).await {
                if let Ok(file_str) = std::str::from_utf8(&file_bytes) {
                    if let Ok(file_toml) = toml::from_str::<ProjectInfo>(file_str) {
                        let fs = PackageFileSystem::new(new_path.clone());
                        info!(
                            "found quill project '{}' at {}",
                            file_toml.name,
                            new_path.to_str().unwrap()
                        );
                        self.root_file_systems
                            .write()
                            .await
                            .file_systems
                            .insert(new_path.clone(), fs);
                        return Some((path.strip_prefix(&new_path).unwrap().into(), new_path));
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
    /// Maps workspace roots to package file systems.
    pub file_systems: HashMap<PathBuf, PackageFileSystem>,
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
        if let Some((identifier, project_root)) =
            self.get_project_root(params.text_document.uri).await
        {
            trace!(
                "file {} in {} changed",
                identifier,
                project_root.to_string_lossy(),
            );
            let contents = params.content_changes[0].text.clone();
            self.root_file_systems.read().await.file_systems[&project_root]
                .overwrite_source_file(identifier, contents)
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
                .remove_cache(identifier)
                .await;
        }
    }

    async fn did_save(&self, _params: DidSaveTextDocumentParams) {
        info!("saved file");
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
