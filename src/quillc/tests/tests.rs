//! This is a testing framework for evaluating the output of `quillc` against
//! sample quill projects designed to stretch the limits of the compiler.
//! Every test case should compile unless a `should_fail` file is present,
//! and if `output.txt` or `error_code.txt` are present the executable should run
//! and produce the given output or error code.
//! Each executed program is given 30 seconds to complete, and then it is considered timed out.
//!
//! To create a new test case, simply create a new quill project somewhere in the `tests` dir.

use std::path::PathBuf;

use quill_target::{BuildInfo, TargetTriple};
use quillc_api::QuillcInvocation;

use quillc::invoke;

// Include the tests automatically generated by the build script.
include!(concat!(env!("OUT_DIR"), "/tests.rs"));

/// Harness for all automated tests.
fn run_test(directory: &str, target_triple: TargetTriple) {
    let code_folder = PathBuf::from("tests")
        .join(directory)
        .canonicalize()
        .unwrap();
    let build_folder = code_folder.join("build");

    // Clean the build folder to clean up from previous tests.
    let _ = std::fs::remove_dir_all(&build_folder);

    // Invoke quillc.
    let compile_result = invoke(QuillcInvocation {
        build_info: BuildInfo {
            target_triple,
            code_folder: code_folder.clone(),
            build_folder: build_folder.clone(),
        },
        zig_compiler: PathBuf::from("zig"),
    });

    // If there was a file named `should_fail` in the project root, this
    // test was expected to fail.
    if code_folder.join("should_fail").exists() {
        assert!(!compile_result);
    } else {
        // The code should have compiled successfully.
        assert!(compile_result);

        // Check to see if we need to run the test's executable.
        // If the `output.txt` or `error_code.txt` file exists, we need to
        // run to verify that the test succeeded.

        let expected_output = std::fs::read_to_string(code_folder.join("output.txt")).ok();
        let expected_code = std::fs::read_to_string(code_folder.join("error_code.txt"))
            .ok()
            .map(|str| str.trim_end().parse::<i32>().unwrap());

        if expected_output.is_some() || expected_code.is_some() {
            // We need to run the executable.
            let expected_code = expected_code.unwrap_or(0);
            let output = if let quill_target::TargetArchitecture::Wasm32 = target_triple.arch {
                // Run the WASM using `wasmtime`.
                let mut command = std::process::Command::new("wasmtime");
                command.arg(build_folder.join("test.wasm"));
                command
            } else {
                // Run the executable directly.
                std::process::Command::new(build_folder.join(if cfg!(target_os = "windows") {
                    "test.exe"
                } else {
                    "test"
                }))
            }
            .output()
            .expect("could not execute command");

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
    }
}
