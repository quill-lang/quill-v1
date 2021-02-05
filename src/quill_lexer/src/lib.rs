pub struct Token {}

#[tokio::test]
async fn test_lexer() {
    use quill_source_file::{PackageFileSystem, SourceFileIdentifier};
    use std::path::PathBuf;

    let fs = PackageFileSystem::new(PathBuf::from("test"));
    fs.with_source_file(
        &SourceFileIdentifier {
            module: vec![].into(),
            file: "file".into(),
        },
        |source| match source {
            Ok(source) => {
                println!("source loaded, content:");
                println!("{}", source.get_contents());
            }
            Err(err) => {
                panic!("could not open source file: {:?}", err)
            }
        },
    )
    .await;
}
