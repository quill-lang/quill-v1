use std::{
    path::Path,
    process::{Command, Stdio},
};

use quill_target::BuildInfo;

pub fn link(project_name: &str, zig_compiler: &Path, build_info: BuildInfo) {
    let mut linker = Command::new(zig_compiler);
    linker.arg("build-exe");
    linker.arg("-target");
    linker.arg(build_info.target_triple.to_zig_target());
    linker.arg("--library");
    linker.arg("c");
    linker.arg("--name");
    linker.arg(build_info.build_folder.join(project_name));
    linker.arg(build_info.build_folder.join("out.o"));
    linker.stderr(Stdio::inherit());
    let result = linker.output().unwrap();
    if !result.status.success() {
        panic!("linker failed");
    }
}
