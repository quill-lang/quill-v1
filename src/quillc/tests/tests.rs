//! This is a testing framework for evaluating the output of `quillc` against
//! sample quill projects designed to stretch the limits of the compiler.
//! Every test case under `should_compile` should compile;
//! every test case under `should_fail` should not compile;
//! and every test case under `check_output` should:
//! - compile;
//! - give the output which is stored in `output.txt` (if present, and encoded as UTF-8)
//!   emitted to the standard output stream, ignoring trailing whitespace; and
//! - exit with the error code specified in `error_code.txt` (if present; if absent assumed code 0).
//! Each executed program is given 10 seconds to complete, and then it is considered timed out.

use std::{path::PathBuf, time::Duration};

use quill_target::{BuildInfo, TargetTriple};
use quillc_api::QuillcInvocation;
use test_case::test_case;

use quillc::invoke;

#[allow(clippy::unused_unit)]
#[test_case("io_putchar/ascii")]
#[tokio::test]
async fn check_output(directory: &str) {
    let code_folder = PathBuf::from("tests")
        .join(directory)
        .canonicalize()
        .unwrap();
    let build_folder = code_folder.join("build");
    let _ = tokio::fs::remove_dir_all(&build_folder).await;

    invoke(QuillcInvocation {
        build_info: BuildInfo {
            target_triple: TargetTriple::default_triple(),
            code_folder: code_folder.clone(),
            build_folder: build_folder.clone(),
        },
        zig_compiler: PathBuf::from("zig"),
    })
    .await
    .unwrap();

    let output = tokio::time::timeout(
        Duration::from_secs(10),
        tokio::process::Command::new(build_folder.join(if cfg!(target_os = "windows") {
            "test.exe"
        } else {
            "test"
        }))
        .output(),
    )
    .await
    .expect("timed out")
    .expect("could not execute command");

    let expected_output = tokio::fs::read_to_string(code_folder.join("output.txt"))
        .await
        .ok();
    let expected_code = tokio::fs::read_to_string(code_folder.join("error_code.txt"))
        .await
        .ok()
        .map_or(0, |str| str.trim_end().parse::<i32>().unwrap());

    let code_mismatch = Some(expected_code) != output.status.code();
    let output_mismatch = expected_output.as_deref().map_or(false, |expected| {
        expected.trim_end() != std::str::from_utf8(&output.stdout).unwrap().trim_end()
    });

    if code_mismatch || output_mismatch {
        panic!(
            "output did not match:\nexpected code {}, expected output:\n{}\n\ngot code {}, got output:\n{}\n",
            expected_code,
            expected_output.as_deref().map(|s| s.trim_end()).unwrap_or_else(|| "<nothing>"),
            output.status.code().map(|code| code.to_string()).unwrap_or_else(|| "<no code>".to_string()),
            std::str::from_utf8(&output.stdout).unwrap().trim_end()
        );
    }
}

#[allow(clippy::unused_unit)]
#[test_case("check_main_function/successful")]
#[tokio::test]
async fn should_compile(directory: &str) {
    let code_folder = PathBuf::from("tests")
        .join(directory)
        .canonicalize()
        .unwrap();
    let build_folder = code_folder.join("build");
    let _ = tokio::fs::remove_dir_all(&build_folder).await;

    invoke(QuillcInvocation {
        build_info: BuildInfo {
            target_triple: TargetTriple::default_triple(),
            code_folder,
            build_folder,
        },
        zig_compiler: PathBuf::from("zig"),
    })
    .await
    .unwrap();
}

#[allow(clippy::unused_unit)]
#[test_case("check_main_function/empty_project")]
#[test_case("check_main_function/empty_project_with_main")]
// Register all the regression tests for fixed issues.
#[test_case("regression/0055")]
#[tokio::test]
#[should_panic]
async fn should_fail(directory: &str) {
    let code_folder = PathBuf::from("tests")
        .join(directory)
        .canonicalize()
        .unwrap();
    let build_folder = code_folder.join("build");
    let _ = tokio::fs::remove_dir_all(&build_folder).await;

    invoke(QuillcInvocation {
        build_info: BuildInfo {
            target_triple: TargetTriple::default_triple(),
            code_folder,
            build_folder,
        },
        zig_compiler: PathBuf::from("zig"),
    })
    .await
    .unwrap();
}
