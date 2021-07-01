use std::{
    io::{BufWriter, Write},
    path::{Path, PathBuf},
};

/// Automatically generate the automated test module.
pub fn main() {
    println!("cargo:rerun-if-changed=tests");
    let out_dir = std::env::var("OUT_DIR").unwrap();
    let destination = std::path::Path::new(&out_dir).join("tests.rs");
    let f = std::fs::File::create(&destination).unwrap();

    // Scan for every test.
    scan_dir(
        &mut BufWriter::new(f),
        &PathBuf::from("tests"),
        &PathBuf::new(),
    );
}

fn scan_dir(f: &mut impl Write, root: &Path, suffix: &Path) {
    // Walk through the directory, adding tests as we go.
    for entry in std::fs::read_dir(root.join(suffix)).unwrap() {
        let entry = entry.unwrap();
        let ty = entry.file_type().unwrap();
        if ty.is_dir() {
            let this_suffix = suffix.join(entry.file_name());
            // Is this directory a quill project?
            if entry.path().join("quill.toml").is_file() {
                // Yes. Add a unit test.
                let directory = this_suffix.to_string_lossy().replace('\\', "/");
                let name = directory.replace("/", "_");
                // Ignore the WASM test by default.
                write!(
                    f,
                    r#"
                    #[test]
                    #[ntest::timeout(10_000)]
                    fn {name}() {{
                        run_test("{directory}", TargetTriple::default_triple());
                    }}

                    #[test]
                    #[ignore]
                    #[ntest::timeout(10_000)]
                    fn {name}_wasm() {{
                        run_test("{directory}", TargetTriple::wasm32_wasi());
                    }}
                    "#,
                    name = name,
                    directory = directory,
                )
                .unwrap();
            } else {
                // Recurse to see if this directory contains a quill project.
                scan_dir(f, root, &this_suffix);
            }
        }
    }
}
