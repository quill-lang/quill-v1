mod backend;
mod diagnostic;
mod path;
mod semantic_tokens;

use lspower::{LspService, Server};
use tracing::Level;

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

    let (service, messages) = LspService::new(backend::Backend::new);
    Server::new(stdin, stdout)
        .interleave(messages)
        .serve(service)
        .await;
}
