use std::fmt::Display;

use quill_common::name::QualifiedName;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

impl Type {
    /// If `parenthesise` is true, the parameter should be parenthesised.
    pub fn fmt_proper(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        parenthesise: bool,
    ) -> std::fmt::Result {
        if parenthesise {
            write!(f, "(")?;
        }
        match self {
            Type::Named { name, parameters } => {
                write!(f, "{}", name.name)?;
                if !parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in parameters.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_proper(f, false)?;
                    }
                    write!(f, "]")?;
                }
            }
            Type::Function(left, right) => {
                left.fmt_proper(f, matches!(**left, Type::Function(_, _)))?;
                write!(f, " -> ")?;
                right.fmt_proper(f, false)?;
            }
            Type::Variable {
                variable,
                parameters,
            } => {
                write!(f, "{}", variable)?;
                if !parameters.is_empty() {
                    write!(f, "[")?;
                    for (i, param) in parameters.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        param.fmt_proper(f, false)?;
                    }
                    write!(f, "]")?;
                }
            }
        };
        if parenthesise {
            write!(f, ")")?;
        }
        Ok(())
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_proper(f, false)
    }
}
