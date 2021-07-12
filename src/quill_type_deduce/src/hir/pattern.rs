use std::fmt::Display;

use quill_common::location::{Range, Ranged};
use quill_parser::{expr_pat::ConstantValue, identifier::NameP};
use quill_type::Type;

use crate::TypeConstructorInvocation;

/// A pattern made up of type constructors and potential unknowns.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// A name representing the entire pattern, e.g. `a`.
    Named(NameP),
    /// A constant value.
    Constant { range: Range, value: ConstantValue },
    /// A type constructor, e.g. `False` or `Maybe { value = a }`.
    TypeConstructor {
        type_ctor: TypeConstructorInvocation,
        /// The list of fields. If a pattern is provided, the pattern is matched against the named field.
        /// If no pattern is provided in Quill code, an automatic pattern is created, that simply assigns the field to a new variable with the same name.
        fields: Vec<(NameP, Type, Pattern)>,
    },
    /// An impl, e.g. `impl { print }`.
    Impl {
        impl_token: Range,
        /// The list of fields. If a pattern is provided, the pattern is matched against the named field.
        /// If no pattern is provided in Quill code, an automatic pattern is created, that simply assigns the field to a new variable with the same name.
        fields: Vec<(NameP, Type, Pattern)>,
    },
    /// A function pattern. This cannot be used directly in code,
    /// this is created only for working with functions that have multiple patterns.
    Function {
        param_types: Vec<Type>,
        args: Vec<Pattern>,
    },
    /// A borrow of a pattern.
    Borrow {
        borrow_token: Range,
        borrowed: Box<Pattern>,
    },
    /// An underscore representing an ignored pattern.
    Unknown(Range),
}

impl Ranged for Pattern {
    fn range(&self) -> Range {
        match self {
            Pattern::Named(identifier) => identifier.range,
            Pattern::Constant { range, .. } => *range,
            Pattern::TypeConstructor { type_ctor, fields } => fields
                .iter()
                .fold(type_ctor.range, |acc, (_name, _ty, pat)| {
                    acc.union(pat.range())
                }),
            Pattern::Impl {
                impl_token, fields, ..
            } => fields
                .iter()
                .fold(*impl_token, |acc, (_name, _ty, pat)| acc.union(pat.range())),
            Pattern::Borrow { borrowed, .. } => borrowed.range(),
            Pattern::Unknown(range) => *range,
            Pattern::Function { args, .. } => args
                .iter()
                .fold(args[0].range(), |acc, i| acc.union(i.range())),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Named(identifier) => write!(f, "{}", identifier.name),
            Pattern::Constant { value, .. } => write!(f, "const {}", value),
            Pattern::TypeConstructor { type_ctor, fields } => {
                if fields.is_empty() {
                    return write!(f, "{}", type_ctor.data_type.name);
                }

                write!(f, "{} {{ ", type_ctor.data_type.name)?;
                for (i, (name, _ty, pat)) in fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, " {}", name.name)?;
                    write!(f, " = {}", pat)?;
                }
                write!(f, " }}")
            }
            Pattern::Impl { fields, .. } => {
                if fields.is_empty() {
                    return write!(f, "impl {{}}");
                }

                write!(f, "impl {{ ")?;
                for (i, (name, _ty, pat)) in fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, " {}", name.name)?;
                    write!(f, " = {}", pat)?;
                }
                write!(f, " }}")
            }
            Pattern::Function { args, .. } => {
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                Ok(())
            }
            Pattern::Borrow { borrowed, .. } => write!(f, "&{}", borrowed),
            Pattern::Unknown(_) => write!(f, "_"),
        }
    }
}
