use std::fmt::{Debug, Display};

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
    /// A primitive type, built in to the core of the type system.
    Primitive(PrimitiveType),
}

/// The list of all core types, that are trivially supported by any LLVM output platform.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum PrimitiveType {
    /// The unit type. This does not represent any particular value,
    /// and is defined to take zero memory to represent.
    Unit,
    /// A 64-bit signed integer type.
    Int,
}

impl Debug for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveType::Unit => write!(f, "unit"),
            PrimitiveType::Int => write!(f, "int"),
        }
    }
}

impl Display for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
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
                write!(f, "{}", name)?;
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
            Type::Primitive(prim) => write!(f, "{:?}", prim)?,
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
