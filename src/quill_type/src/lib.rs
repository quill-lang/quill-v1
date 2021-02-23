use quill_common::name::QualifiedName;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either[T, U]`.
    Named {
        name: QualifiedName,
        parameters: Vec<Type>,
    },
    /// A type variable, like `A`. Type variables may contain parameters.
    Variable {
        variable: String,
        parameters: Vec<Type>,
    },
    /// A function `a -> b`.
    /// Functions with more arguments, e.g. `a -> b -> c` are represented as
    /// curried functions, e.g. `a -> (b -> c)`.
    Function(Box<Type>, Box<Type>),
}
