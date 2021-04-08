use std::{collections::HashMap, path::PathBuf, sync::Arc};

use lspower::jsonrpc;
use lspower::lsp::*;
use lspower::{Client, LanguageServer, LspService, Server};
use quill_source_file::PackageFileSystem;
use quillc_api::ProjectInfo;
use tokio::sync::RwLock;
use tracing::{info, Level};

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
    /// in RootFileSystems.
    ///
    /// In particular, this checks parent URIs until a `quill.toml` file is found.
    /// If one is found, then that directory is added to `RootFileSystems` as a file
    /// system root.
    pub async fn get_project_root(&self, url: Url) -> Option<PathBuf> {
        assert!(url.scheme() == "file");
        let mut path = url.to_file_path().unwrap();

        // First, check if we've already loaded this project folder.
        {
            let read = self.root_file_systems.read().await;
            for k in read.file_systems.keys() {
                if path.starts_with(k) {
                    return Some(k.clone());
                }
            }
        }

        loop {
            if let Ok(file_bytes) = tokio::fs::read(path.join("quill.toml")).await {
                if let Ok(file_str) = std::str::from_utf8(&file_bytes) {
                    if let Ok(file_toml) = toml::from_str::<ProjectInfo>(file_str) {
                        let fs = PackageFileSystem::new(path.clone());
                        info!(
                            "found quill project '{}' at {}",
                            file_toml.name,
                            path.to_str().unwrap()
                        );
                        self.root_file_systems
                            .write()
                            .await
                            .file_systems
                            .insert(path.clone(), fs);
                        return Some(path);
                    }
                }
            }

            if !path.pop() {
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

    async fn did_open(&self, _params: DidOpenTextDocumentParams) {
        info!("opened file");
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        // Since we're using full text document synchronisation, we can just get the first change and that will be the whole document.
        info!("file {} changed", params.text_document.uri);
        if let Some(project_root) = self.get_project_root(params.text_document.uri).await {
            info!("file was in root {}", project_root.to_str().unwrap());
        }
        let content = params.content_changes[0].text.clone();
    }

    async fn did_close(&self, _params: DidCloseTextDocumentParams) {
        info!("closed file");
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
