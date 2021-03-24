pub(crate) mod index_resolve;
pub mod type_check;
pub(crate) mod type_deduce;
pub(crate) mod type_resolve;

pub use index_resolve::replace_type_variables;
pub use index_resolve::TypeConstructorInvocation;
pub use type_check::check;
