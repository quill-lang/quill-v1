//! This is a testing framework for evaluating the output of `quillc` against
//! sample quill projects designed to stretch the limits of the compiler.
//! Every test case should compile unless a `should_fail` file is present,
//! and if `output.txt` or `error_code.txt` are present the executable should run
//! and produce the given output or error code.
//! Each executed program is given 30 seconds to complete, and then it is considered timed out.
//!
//! To create a new test case, simply create a new quill project somewhere in the `tests` dir.

use std::{
    fs::File,
    path::{Path, PathBuf},
};

use quill_target::{
    BuildInfo, TargetArchitecture, TargetEnvironment, TargetOS, TargetTriple, TargetVendor,
};
use quillc_api::QuillcInvocation;

use quillc::invoke;

// Include the tests automatically generated by the build script.
include!(concat!(env!("OUT_DIR"), "/tests.rs"));

/// A test that compiles the standard library twice, and checks for build determinism.
#[test]
fn build_determinism() {
    let code_folder = PathBuf::from("../../stdlib/core").canonicalize().unwrap();
    let build_folder = code_folder.join("build");
    let other_build_folder = code_folder.join("build_other");

    let triples = [
        TargetTriple {
            arch: TargetArchitecture::X86_64,
            vendor: TargetVendor::Pc,
            os: TargetOS::Windows,
            env: Some(TargetEnvironment::Gnu),
        },
        TargetTriple {
            arch: TargetArchitecture::X86_64,
            vendor: TargetVendor::Unknown,
            os: TargetOS::Linux,
            env: Some(TargetEnvironment::Gnu),
        },
        TargetTriple::wasm32_wasi(),
    ];

    let mut failed = false;

    // Clean the build folder to clean up from previous builds.
    let _ = std::fs::remove_dir_all(&build_folder);
    let _ = std::fs::remove_dir_all(&other_build_folder);

    for target_triple in triples {
        eprintln!("---\ntesting {}\n---", target_triple);

        // Invoke quillc.
        // The release optimisation types should be fully deterministic, but debug builds are not necessarily.
        if !invoke(QuillcInvocation {
            build_info: BuildInfo {
                target_triple,
                code_folder: code_folder.clone(),
                build_folder: build_folder.clone(),

                optimisation_type: quill_target::OptimisationType::ReleaseSafe,
                emit_hir: false,
                emit_mir: false,
                emit_project_mir: true,
                emit_unverified_llvm_ir: true,
                emit_basic_llvm_ir: true,
                emit_llvm_ir: true,
                emit_asm: true,
            },
            zig_compiler: PathBuf::from("zig"),
        }) {
            eprintln!("target triple {} could not compile", target_triple);
            failed = true;
        }

        // Cache the build artifacts.
        std::fs::rename(&build_folder, &other_build_folder).unwrap();

        // Invoke quillc a second time.
        if !invoke(QuillcInvocation {
            build_info: BuildInfo {
                target_triple,
                code_folder: code_folder.clone(),
                build_folder: build_folder.clone(),

                optimisation_type: quill_target::OptimisationType::ReleaseSafe,
                emit_hir: false,
                emit_mir: false,
                emit_project_mir: true,
                emit_unverified_llvm_ir: true,
                emit_basic_llvm_ir: true,
                emit_llvm_ir: true,
                emit_asm: true,
            },
            zig_compiler: PathBuf::from("zig"),
        }) {
            eprintln!(
                "target triple {} could not compile (for the second time",
                target_triple
            );
            failed = true;
        }

        // Check if the files match exactly.
        let mut diff = |name: &str, path1: &Path, path2: &Path| {
            eprintln!("running diff {} on target triple {}", name, target_triple);
            let mut file1 = match File::open(path1) {
                Ok(f) => f,
                Err(e) => panic!("{}", e),
            };
            let mut file2 = match File::open(path2) {
                Ok(f) => f,
                Err(e) => panic!("{}", e),
            };
            if !file_diff::diff_files(&mut file1, &mut file2) {
                eprintln!(
                    "MISMATCH: target triple {} failed to build deterministically ({})",
                    target_triple, name
                );
                failed = true;
            }
        };

        let exe_name = if let quill_target::TargetArchitecture::Wasm32 = target_triple.arch {
            "core.wasm"
        } else if let TargetOS::Windows = target_triple.os {
            "core.exe"
        } else {
            "core"
        };

        let target_folder = build_folder.join(target_triple.to_string());
        let other_target_folder = other_build_folder.join(target_triple.to_string());

        diff(
            "mir",
            &build_folder.join("out.mir"),
            &other_build_folder.join("out.mir"),
        );
        diff(
            "basic.ll",
            &target_folder.join("out.basic.ll"),
            &other_target_folder.join("out.basic.ll"),
        );
        diff(
            "ll",
            &target_folder.join("out.ll"),
            &other_target_folder.join("out.ll"),
        );
        diff(
            "asm",
            &target_folder.join("out.asm"),
            &other_target_folder.join("out.asm"),
        );
        diff(
            "obj",
            &target_folder.join("out.o"),
            &other_target_folder.join("out.o"),
        );
        // FIXME: If we're on Windows, we're allowed to have mismatched executables, since the link timestamp gets
        // embedded in the exe. We can't change this setting currently in the Zig compiler.
        if !matches!(target_triple.os, TargetOS::Windows) {
            diff(
                "exe",
                &target_folder.join(exe_name),
                &other_target_folder.join(exe_name),
            );
        }

        // Store the build folder for later inspection.
        let stored_build_artifacts =
            build_folder.with_file_name(format!("build_{}", target_triple));
        let _ = std::fs::remove_dir_all(&stored_build_artifacts);
        std::fs::create_dir(&stored_build_artifacts).unwrap();
        // eprintln!("from {:?} to {:?}", build_folder, stored_build_artifacts);
        fs_extra::dir::move_dir(&build_folder, &stored_build_artifacts, &Default::default())
            .unwrap();
        fs_extra::dir::move_dir(
            &other_build_folder,
            stored_build_artifacts,
            &Default::default(),
        )
        .unwrap();
    }

    assert!(!failed);
}

/// Harness for all automated tests.
fn run_test(directory: &str, target_triple: TargetTriple) {
    let code_folder = PathBuf::from("tests")
        .join(directory)
        .canonicalize()
        .unwrap();
    let build_folder = code_folder.join("build");

    // Clean the build target folder to clean up from previous tests.
    let target_folder = build_folder.join(target_triple.to_string());
    let _ = std::fs::remove_dir_all(&target_folder);

    // Invoke quillc.
    let compile_result = invoke(QuillcInvocation {
        build_info: BuildInfo {
            target_triple,
            code_folder: code_folder.clone(),
            build_folder,

            optimisation_type: quill_target::OptimisationType::Debug,
            emit_hir: false,
            emit_mir: false,
            emit_project_mir: false,
            emit_unverified_llvm_ir: false,
            emit_basic_llvm_ir: false,
            emit_llvm_ir: false,
            emit_asm: false,
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
                command.arg(target_folder.join("test.wasm"));
                command
            } else {
                // Run the executable directly.
                std::process::Command::new(target_folder.join(if cfg!(target_os = "windows") {
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

            assert!(!(code_mismatch || output_mismatch), "output did not match:\nexpected code {}, expected output:\n{}\n\ngot code {}, got output:\n{}\n",
                    expected_code,
                    expected_output.as_deref().map(|s| s.trim_end()).unwrap_or_else(|| "<nothing>"),
                    output.status.code().map(|code| code.to_string()).unwrap_or_else(|| "<no code>".to_string()),
                    std::str::from_utf8(&output.stdout).unwrap().trim_end());
        }
    }
}
