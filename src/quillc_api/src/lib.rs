use quill_target::BuildInfo;
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
pub struct QuillcInvocation {
    pub build_info: BuildInfo,
}
