//! Although not required for builds, some of the structures here implement Hash for
//! ariadne's error reporting.

use std::{
    fmt::{Debug, Display},
    path::PathBuf,
};

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Location {
    /// A 0-indexed line number.
    pub line: u32,
    /// A 0-indexed column number.
    pub col: u32,
}

impl Location {
    pub fn new(line: u32, col: u32) -> Self {
        Self { line, col }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:0>3}:{:0>3}", self.line + 1, self.col + 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Range {
    /// The start of this range of characters, inclusive.
    pub start: Location,
    /// The end of this range of characters, exclusive.
    pub end: Location,
}

impl Display for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} - {}", self.start, self.end)
    }
}

impl From<Location> for Range {
    fn from(location: Location) -> Self {
        Self {
            start: location,
            end: Location {
                line: location.line,
                col: location.col + 1,
            },
        }
    }
}

impl Range {
    pub fn union(self, other: Range) -> Range {
        Range {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

pub trait Ranged {
    fn range(&self) -> Range;
}

impl Ranged for Range {
    fn range(&self) -> Range {
        *self
    }
}

/// A fragment of the canonical name for a source file.
/// This does not include things like slashes to separate directories, double periods to denote going up a directory, or file extensions.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceFileIdentifierSegment(pub String);

impl Debug for SourceFileIdentifierSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for SourceFileIdentifierSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl<S> From<S> for SourceFileIdentifierSegment
where
    S: Into<String>,
{
    fn from(s: S) -> Self {
        SourceFileIdentifierSegment(s.into())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ModuleIdentifier {
    pub segments: Vec<SourceFileIdentifierSegment>,
}

impl Debug for ModuleIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, fragment) in self.segments.iter().enumerate() {
            if i != 0 {
                write!(f, "::")?;
            }
            write!(f, "{}", fragment)?;
        }
        Ok(())
    }
}

impl Display for ModuleIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl From<Vec<String>> for ModuleIdentifier {
    fn from(segments: Vec<String>) -> Self {
        Self {
            segments: segments
                .into_iter()
                .map(SourceFileIdentifierSegment)
                .collect(),
        }
    }
}

impl From<ModuleIdentifier> for PathBuf {
    fn from(identifier: ModuleIdentifier) -> Self {
        identifier
            .segments
            .into_iter()
            .map(|fragment| fragment.0)
            .collect()
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct SourceFileIdentifier {
    pub module: ModuleIdentifier,
    pub file: SourceFileIdentifierSegment,
    pub file_type: SourceFileType,
}

/// This implements Ord to make Quill builds reproducible.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum SourceFileType {
    Quill,
    Toml,
}

impl Display for SourceFileType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SourceFileType::Quill => write!(f, "Quill source file"),
            SourceFileType::Toml => write!(f, "TOML file"),
        }
    }
}

impl SourceFileType {
    pub fn file_extension(&self) -> &'static str {
        match self {
            SourceFileType::Quill => "ql",
            SourceFileType::Toml => "toml",
        }
    }
}

impl Debug for SourceFileIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.module.segments.is_empty() {
            write!(f, "{}", self.file)
        } else {
            write!(f, "{}::{}", self.module, self.file)
        }
    }
}

impl Display for SourceFileIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}
