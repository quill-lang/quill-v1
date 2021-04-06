use std::path::PathBuf;

use quill_target::BuildInfo;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct QuillcInvocation {
    pub build_info: BuildInfo,
    pub deps_directory: PathBuf,
}

/// This is the format for `quill.toml` files.
#[derive(Debug, Serialize, Deserialize)]
pub struct ProjectInfo {
    pub name: String,
}
