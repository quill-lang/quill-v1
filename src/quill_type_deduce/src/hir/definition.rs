use quill_common::location::{Range, Ranged};
use quill_index::TypeParameter;
use quill_type::Type;

use super::{expr::Expression, pattern::Pattern};

/// A definition for a symbol, i.e. a function or constant.
/// The function's type is `arg_types -> return_type`.
/// For example, if we defined a function
/// ```notrust
/// def foo: int -> int -> int {
///     foo a b = a
/// }
/// ```
/// then `arg_types` would be `[int, int]` and `return_type` would be `int`. If instead we defined it as
/// ```notrust
/// def foo: int -> int -> int {
///     foo a = \b -> a
/// }
/// ```
/// then `arg_types` would be `[int]` and `return_type` would be `int -> int`.
#[derive(Debug)]
pub struct Definition {
    pub range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<TypeParameter>,
    pub arg_types: Vec<Type>,
    pub return_type: Type,
    pub body: DefinitionBody,
}

#[derive(Debug)]
pub enum DefinitionBody {
    PatternMatch(Vec<DefinitionCase>),
    CompilerIntrinsic,
}

impl Ranged for Definition {
    fn range(&self) -> Range {
        self.range
    }
}

#[derive(Debug)]
pub struct DefinitionCase {
    pub range: Range,
    pub arg_patterns: Vec<Pattern>,
    pub replacement: Expression,
}
