//! Resolves an unqualified name into a fully qualified name with type information.

use std::sync::atomic::{AtomicU64, Ordering};

/// An unknown type, used for intermediate values of expressions that we don't know the type of.
/// To generate a new type variable, call `default`.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct TypeVariableId(u64);
static TYPE_VARIABLE_ID_GENERATOR: AtomicU64 = AtomicU64::new(0);

impl Default for TypeVariableId {
    fn default() -> Self {
        Self(TYPE_VARIABLE_ID_GENERATOR.fetch_add(1, Ordering::Relaxed))
    }
}
