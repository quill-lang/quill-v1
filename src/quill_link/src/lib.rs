use std::{
    path::{Path, PathBuf},
    process::Command,
};

use quill_llvm::{BuildInfo, TargetOS};

/// The `deps` path is a path to the folder containing files such as `ld.lld` and `msvcrt.lib`.
pub fn link(deps: &Path, build_info: BuildInfo) {
    // Invoke `lld_link` to link for windows, and `ld.lld` to link for linux.
    match build_info.target_triple.os {
        TargetOS::Linux => {
            // Run `ld.lld`.
        }
        TargetOS::Windows => {
            // Run `lld-link`.
            let mut linker = lld_link(deps);

            linker.arg(format!(
                "/OUT:{}",
                build_info.build_folder.join("out.exe").to_str().unwrap()
            ));
            linker.arg(build_info.build_folder.join("out.o"));
            linker.arg(dep_win(deps, "msvcrt.lib"));
            linker.arg(dep_win(deps, "kernel32.lib"));
            linker.arg(dep_win(deps, "ucrt.lib"));
            linker.arg(dep_win(deps, "vcruntime.lib"));

            let result = linker.output().unwrap();
            if !result.status.success() {
                panic!(
                    "Linker failed:\n{}",
                    std::str::from_utf8(&result.stderr).unwrap()
                );
            }
        }
    }
}

#[cfg(target_family = "windows")]
fn lld_link(deps: &Path) -> Command {
    Command::new(deps.join("dev-win").join("lld-link.exe"))
}

#[cfg(target_family = "unix")]
fn lld_link(deps: &Path) -> Command {
    let mut command = Command::new(deps.join("dev-ubuntu-16.04").join("lld"));
    command.arg("-flavor").arg("link");
    command
}

fn dep_win(deps: &Path, dep: &str) -> PathBuf {
    deps.join("target-win").join(dep)
}
