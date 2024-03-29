//! Resolves an unqualified name into a fully qualified name with type information.

use std::sync::atomic::{AtomicU64, Ordering};

use crate::hir::expr::TypeVariable;

/// An unknown type, used for intermediate values of expressions that we don't know the type of.
/// To generate a new type variable, call `default`.
/// This implements Ord to make Quill builds reproducible.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct TypeVariableId(u64);
static TYPE_VARIABLE_ID_GENERATOR: AtomicU64 = AtomicU64::new(0);

impl Default for TypeVariableId {
    fn default() -> Self {
        Self(TYPE_VARIABLE_ID_GENERATOR.fetch_add(1, Ordering::Relaxed))
    }
}

impl From<TypeVariableId> for TypeVariable {
    fn from(id: TypeVariableId) -> Self {
        TypeVariable::Unknown { id }
    }
}
