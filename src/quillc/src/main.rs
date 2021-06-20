/// The `quillc` compiler is not intended to be used as a CLI.
/// Rather, the `quill` driver program should supply correct arguments to `quillc` in the form of JSON.
#[tokio::main]
async fn main() {
    let invocation: quillc_api::QuillcInvocation =
        serde_json::from_str(&std::env::args().nth(1).unwrap()).unwrap();

    if quillc::invoke(invocation).await.is_err() {
        std::process::exit(1);
    }
}
