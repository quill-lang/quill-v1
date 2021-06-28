use std::fmt::Debug;

use quill_common::location::Range;

#[derive(Clone, Copy)]
pub enum Visibility {
    Public(Range),
    Private,
}

impl Debug for Visibility {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Visibility::Public(_) => write!(f, "public"),
            Visibility::Private => write!(f, "private"),
        }
    }
}
