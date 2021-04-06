use std::{
    fmt::{Debug, Display},
    path::PathBuf,
};

#[derive(Clone, Copy)]
pub struct TargetTriple {
    pub arch: TargetArchitecture,
    pub vendor: TargetVendor,
    pub os: TargetOS,
    pub env: Option<TargetEnvironment>,
}

impl Display for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(env) = &self.env {
            write!(f, "{}-{}-{}-{}", self.arch, self.vendor, self.os, env)
        } else {
            write!(f, "{}-{}-{}", self.arch, self.vendor, self.os)
        }
    }
}

impl Debug for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

#[derive(Clone, Copy)]
pub enum TargetArchitecture {
    X86_64,
}

impl Display for TargetArchitecture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetArchitecture::X86_64 => "x86_64",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetVendor {
    Unknown,
    Pc,
}

impl Display for TargetVendor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetVendor::Unknown => "unknown",
                TargetVendor::Pc => "pc",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetOS {
    Linux,
    Windows,
}

impl Display for TargetOS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetOS::Linux => "linux",
                TargetOS::Windows => "windows",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetEnvironment {
    Gnu,
    Msvc,
}

impl Display for TargetEnvironment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetEnvironment::Gnu => "gnu",
                TargetEnvironment::Msvc => "msvc",
            }
        )
    }
}

#[derive(Debug, Clone)]
pub struct BuildInfo {
    pub target_triple: TargetTriple,
    pub code_folder: PathBuf,
    pub build_folder: PathBuf,
}
