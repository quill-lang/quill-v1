use either::Either;
use io::BufReader;
use serde::{Deserialize, Serialize};
use tokio::io::AsyncBufReadExt;
use tokio::io::{self, AsyncReadExt, AsyncWriteExt};
use tracing::{info, trace, Level};
use tracing_subscriber::FmtSubscriber;

#[tokio::main]
async fn main() {
    real_main().await.unwrap();
}

struct MessageReader<R> {
    inner: BufReader<R>,
}

impl<R> MessageReader<R>
where
    R: AsyncReadExt + Unpin,
{
    async fn read_message(&mut self) -> io::Result<String> {
        let mut content_length = 0;
        loop {
            let mut line = String::new();
            self.inner.read_line(&mut line).await?;
            // Remove the `\r` at the end of the line.
            let line = line.trim();
            trace!("Reading line {}", line);
            if line.is_empty() {
                break;
            } else if let Some(line) = line.strip_prefix("Content-Length: ") {
                content_length = line.parse().unwrap();
            }
        }
        trace!("Reading length {}", content_length);
        let mut buf = vec![0; content_length];
        self.inner.read_exact(&mut buf).await?;
        let result = String::from_utf8(buf).unwrap();
        trace!("Done {}", result);
        Ok(result)
    }
}

#[derive(Deserialize)]
struct JsonRpcRequest {
    // Must be "2.0".
    jsonrpc: String,
    #[serde(with = "either::serde_untagged_optional")]
    id: Option<Either<String, i32>>,
    method: String,
    params: Option<serde_json::Value>,
}

#[derive(Serialize)]
struct JsonRpcResponse {
    // Must be "2.0".
    jsonrpc: String,
    result: Option<serde_json::Value>,
    error: Option<JsonRpcError>,
    #[serde(with = "either::serde_untagged_optional")]
    id: Option<Either<String, i32>>,
}

#[derive(Serialize)]
struct JsonRpcError {
    code: i32,
    message: String,
    data: serde_json::Value,
}

async fn real_main() -> io::Result<()> {
    let subscriber = FmtSubscriber::builder()
        .with_writer(std::io::stderr)
        .with_max_level(Level::TRACE)
        .with_ansi(false)
        .finish();
    tracing::subscriber::set_global_default(subscriber).unwrap();

    info!("initialising language server");

    let stdin = io::stdin();
    let mut reader = MessageReader {
        inner: io::BufReader::new(stdin),
    };
    let stdout = io::stdout();
    let mut writer = io::BufWriter::new(stdout);

    info!("language server initialised");
    loop {
        let message = reader.read_message().await?;
        let response = match serde_json::from_str::<JsonRpcRequest>(&message) {
            Ok(request) => respond_to_request(request).await,
            Err(err) => JsonRpcResponse {
                jsonrpc: "2.0".to_string(),
                result: None,
                error: Some(JsonRpcError {
                    code: -32600,
                    message: err.to_string(),
                    data: serde_json::Value::Null,
                }),
                id: None,
            },
        };

        let str = serde_json::to_string(&response).unwrap();
        trace!("Responding {}", str);
        let header = format!("Content-Length: {}\r\n\r\n", str.len());
        writer.write_all(header.as_bytes()).await?;
        writer.write_all(str.as_bytes()).await?;
    }
    info!("language server closed");

    Ok(())
}

async fn respond_to_request(request: JsonRpcRequest) -> JsonRpcResponse {
    JsonRpcResponse {
        jsonrpc: request.jsonrpc,
        result: None,
        error: Some(JsonRpcError {
            code: -32000,
            message: "test response is working".to_string(),
            data: serde_json::Value::Null,
        }),
        id: request.id,
    }
}
