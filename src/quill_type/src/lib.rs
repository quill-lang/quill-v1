use std::fmt::{Debug, Display};

use quill_common::name::QualifiedName;

/// This implements Ord to make Quill builds reproducible.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    Borrow {
        ty: Box<Type>,
        /// If we know the borrow condition, give it here.
        borrow: Option<BorrowCondition>,
    },
    /// An implementation of an aspect.
    Impl {
        name: QualifiedName,
        parameters: Vec<Type>,
    },
}

/// Represents the loan conditions of a borrowed value.
/// This implements Ord to make Quill builds reproducible.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct BorrowCondition {
    pub lifetime: Lifetime,
}

impl Display for BorrowCondition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "&{}", self.lifetime)
    }
}

/// This implements Ord to make Quill builds reproducible.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lifetime {
    pub name: String,
}

impl Display for Lifetime {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "'{}", self.name)
    }
}

/// The list of all core types, that are trivially supported by any LLVM output platform.
/// This implements Ord to make Quill builds reproducible.
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PrimitiveType {
    /// The unit type. This does not represent any particular value,
    /// and is defined to take zero memory to represent.
    Unit,
    /// A 1-bit boolean type.
    Bool,
    /// A 64-bit signed integer type.
    Int,
}

impl Debug for PrimitiveType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimitiveType::Unit => write!(f, "Unit"),
            PrimitiveType::Bool => write!(f, "Bool"),
            PrimitiveType::Int => write!(f, "Int"),
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
            Type::Borrow { ty, borrow } => {
                if let Some(borrow) = borrow {
                    write!(f, "{} {}", borrow, ty)?;
                } else {
                    write!(f, "&{}", ty)?;
                }
            }
            Type::Impl { name, parameters } => {
                write!(f, "impl {}", name)?;
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

    /// Removes lifetimes from this type.
    /// This means that &'a T and &'b T will compare equal after this step.
    pub fn anonymise_borrows(self) -> Type {
        match self {
            Type::Named { name, parameters } => Type::Named {
                name,
                parameters: parameters
                    .into_iter()
                    .map(Self::anonymise_borrows)
                    .collect(),
            },
            Type::Variable {
                variable,
                parameters,
            } => Type::Variable {
                variable,
                parameters: parameters
                    .into_iter()
                    .map(Self::anonymise_borrows)
                    .collect(),
            },
            Type::Function(l, r) => Type::Function(
                Box::new(l.anonymise_borrows()),
                Box::new(r.anonymise_borrows()),
            ),
            Type::Primitive(prim) => Type::Primitive(prim),
            Type::Borrow { ty, .. } => Type::Borrow { ty, borrow: None },
            Type::Impl { name, parameters } => Type::Impl {
                name,
                parameters: parameters
                    .into_iter()
                    .map(Self::anonymise_borrows)
                    .collect(),
            },
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.fmt_proper(f, false)
    }
}
