// The type checker will be completely overhauled soon, so we won't worry about keeping it that clean.
#![allow(dead_code)]
#![allow(clippy::large_enum_variant)]

pub(crate) mod hindley_milner;
pub mod hir;
pub(crate) mod index_resolve;
pub mod type_check;
pub(crate) mod type_resolve;

pub use index_resolve::replace_type_variables;
pub use index_resolve::TypeConstructorInvocation;
pub use type_check::check;
