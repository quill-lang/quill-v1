use std::{
    path::{Path, PathBuf},
    process::Command,
};

use quill_target::{BuildInfo, TargetOS};

/// The `deps` path is a path to the folder containing files such as `ld.lld` and `msvcrt.lib`.
pub fn link(project_name: &str, deps: &Path, build_info: BuildInfo) {
    // Invoke `lld_link` to link for windows, and `ld.lld` to link for linux.
    match build_info.target_triple.os {
        TargetOS::Linux => {
            // Run `ld.lld`.
            let mut linker = ld_lld(deps);

            linker.arg("-dynamic-linker");
            linker.arg("/lib64/ld-linux-x86-64.so.2");
            linker.arg("-pie");
            linker.arg("-o");
            linker.arg(build_info.build_folder.join(project_name).to_str().unwrap());
            linker.arg(&format!("-L{}", dep_linux(deps, "").to_str().unwrap()));

            linker.arg(dep_linux(deps, "Scrt1.o").to_str().unwrap());
            linker.arg(dep_linux(deps, "crti.o").to_str().unwrap());
            linker.arg(dep_linux(deps, "crtbeginS.o").to_str().unwrap());
            linker.arg(build_info.build_folder.join("out.o"));

            linker.arg("-lgcc");
            linker.arg("--push-state");
            linker.arg("--as-needed");
            linker.arg("-lgcc_s");
            linker.arg("--pop-state");

            linker.arg("-lc");
            linker.arg("-lc_nonshared");

            linker.arg("-lgcc");
            linker.arg("--push-state");
            linker.arg("--as-needed");
            linker.arg("-lgcc_s");
            linker.arg("--pop-state");

            linker.arg(dep_linux(deps, "crtendS.o").to_str().unwrap());
            linker.arg(dep_linux(deps, "crtn.o").to_str().unwrap());

            let result = linker.output().unwrap();
            if !result.status.success() {
                panic!(
                    "Linker failed:\n{}",
                    std::str::from_utf8(&result.stderr).unwrap()
                );
            }
        }
        TargetOS::Windows => {
            // Run `lld-link`.
            let mut linker = lld_link(deps);

            linker.arg(format!(
                "/OUT:{}",
                build_info
                    .build_folder
                    .join(format!("{}.exe", project_name))
                    .to_str()
                    .unwrap()
            ));
            linker.arg("/DEBUG");
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
fn ld_lld(deps: &Path) -> Command {
    let mut command = Command::new(deps.join("dev-win").join("lld.exe"));
    command.arg("-flavor").arg("ld");
    command
}

#[cfg(target_family = "unix")]
fn ld_lld(deps: &Path) -> Command {
    let mut command = Command::new(deps.join("dev-linux").join("lld"));
    command.arg("-flavor").arg("ld");
    command
}

#[cfg(target_family = "windows")]
fn lld_link(deps: &Path) -> Command {
    let mut command = Command::new(deps.join("dev-win").join("lld.exe"));
    command.arg("-flavor").arg("link");
    command
}

#[cfg(target_family = "unix")]
fn lld_link(deps: &Path) -> Command {
    let mut command = Command::new(deps.join("dev-linux").join("lld"));
    command.arg("-flavor").arg("link");
    command
}

fn dep_linux(deps: &Path, dep: &str) -> PathBuf {
    deps.join("target-linux").join(dep)
}

fn dep_win(deps: &Path, dep: &str) -> PathBuf {
    deps.join("target-win").join(dep)
}
