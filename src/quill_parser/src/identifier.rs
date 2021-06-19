use std::{fmt::Display, hash::Hash};

use quill_common::location::{Range, Ranged};

/// An unresolved identifier, which is a string of text at some range in code.
#[derive(Debug, Clone)]
pub struct IdentifierP {
    /// Must contain at least one segment.
    pub segments: Vec<NameP>,
}

#[derive(Debug, Clone)]
pub(crate) struct Operator {
    pub(crate) level: u32,
    pub(crate) name: NameP,
    pub(crate) ty: AssociativityType,
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum AssociativityType {
    NonAssociative,
    InfixR,
    InfixL,
}

impl IdentifierP {
    /// If this identifier represents a name that has a level of associativity,
    /// Returns the properties of the given operator.
    pub(crate) fn as_operator(&self) -> Option<Operator> {
        if let Some(name) = self.segments.last() {
            as_operator_inner(name.clone())
        } else {
            None
        }
    }
}

/// Returns the properties of the given operator.
fn as_operator_inner(name: NameP) -> Option<Operator> {
    let n = name.name.as_str();
    if name.name.as_str().chars().next().unwrap().is_alphanumeric() {
        None
    } else {
        Some(if n.contains(':') {
            Operator {
                level: 5,
                name,
                ty: AssociativityType::InfixR,
            }
        } else if n.contains('+') || n.contains('-') {
            Operator {
                level: 10,
                name,
                ty: AssociativityType::InfixL,
            }
        } else if n.contains('*') || n.contains('/') {
            Operator {
                level: 15,
                name,
                ty: AssociativityType::InfixL,
            }
        } else if n.contains('=') || n.contains('<') || n.contains('>') {
            Operator {
                level: 3,
                name,
                ty: AssociativityType::NonAssociative,
            }
        } else {
            Operator {
                level: 1,
                name,
                ty: AssociativityType::InfixL,
            }
        })
    }
}

impl Ranged for IdentifierP {
    fn range(&self) -> Range {
        self.segments
            .iter()
            .fold(self.segments[0].range, |range, segment| {
                range.union(segment.range)
            })
    }
}

impl Display for IdentifierP {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, segment) in self.segments.iter().enumerate() {
            if i != 0 {
                write!(f, "::")?;
            }
            write!(f, "{}", segment)?;
        }
        Ok(())
    }
}

/// A name for an item, which cannot be qualified.
#[derive(Debug, Clone, Eq)]
pub struct NameP {
    pub name: String,
    pub range: Range,
}

impl PartialEq for NameP {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

impl Hash for NameP {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.name.hash(state)
    }
}

impl Display for NameP {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
