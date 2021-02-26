use std::fmt::{Debug, Display};

use crate::location::{Range, SourceFileIdentifier};

/// A fully qualified name referring to a top-level item declared in a `.quill` file.
/// This should not be used for qualified identifiers, since in this case we need to also keep track
/// of where the identifier was written; this type is concerned only with the name itself.
#[derive(Clone, PartialEq, Eq)]
pub struct QualifiedName {
    /// The source file path that the name was defined at, not the path at which the name was used.
    pub source_file: SourceFileIdentifier,
    /// The local name within the module.
    pub name: String,
    /// The range that the name was defined at, not the range the name was used.
    pub range: Range,
}

impl Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}::{}", self.source_file, self.name)
    }
}

impl Debug for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}
