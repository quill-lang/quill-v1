use std::fmt::Display;

use quill_common::location::{Range, Ranged};

use crate::identifier::{IdentifierP, NameP};

/// Represents either an expression or a pattern.
#[derive(Debug)]
pub enum ExprPatP {
    /// A named variable e.g. `x` or `+`.
    Variable(IdentifierP),
    /// A primitive constant such as `14` or `false`.
    Immediate { range: Range, value: ConstantValue },
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<ExprPatP>, Box<ExprPatP>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<NameP>,
        expr: Box<ExprPatP>,
    },
    /// A let statement, specifically `let identifier = left_expr;`.
    /// This kind of statement is only valid as an intermediate statement in a block.
    Let {
        let_token: Range,
        name: NameP,
        expr: Box<ExprPatP>,
    },
    /// A block of statements, inside parentheses, separated by newlines,
    /// where the final expression in the block is the type of the block as a whole.
    Block {
        open_bracket: Range,
        close_bracket: Range,
        statements: Vec<ExprPatP>,
    },
    /// Borrow some data for a duration less than its full lifetime.
    Borrow {
        borrow_token: Range,
        expr: Box<ExprPatP>,
    },
    /// Copy some data behind a borrow.
    Copy {
        copy_token: Range,
        expr: Box<ExprPatP>,
    },
    /// The name of a data type, followed by brace brackets containing the data structure's fields.
    ConstructData {
        data_constructor: IdentifierP,
        open_brace: Range,
        close_brace: Range,
        fields: ConstructDataFields,
    },
    /// An underscore `_` representing an unknown.
    /// This is valid only in patterns, not normal expressions.
    Unknown(Range),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ConstantValue {
    Unit,
    Bool(bool),
    Int(i64),
}

impl Display for ConstantValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConstantValue::Unit => write!(f, "unit"),
            ConstantValue::Bool(value) => write!(f, "bool {}", value),
            ConstantValue::Int(value) => write!(f, "int {}", value),
        }
    }
}

#[derive(Debug)]
pub struct ConstructDataFields {
    /// Fields that have been assigned values, e.g. `foo = 1`.
    pub fields: Vec<(NameP, ExprPatP)>,
    /// Fields that have not been assigned values (so will inherit their value from the local variable with that name), e.g. `foo`.
    /// This is useful in patterns, where fields are often not assigned different names.
    pub auto_fields: Vec<NameP>,
}

impl Ranged for ExprPatP {
    fn range(&self) -> Range {
        match self {
            ExprPatP::Variable(identifier) => identifier.range(),
            ExprPatP::Immediate { range, .. } => *range,
            ExprPatP::Apply(left, right) => left.range().union(right.range()),
            ExprPatP::Unknown(range) => *range,
            ExprPatP::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExprPatP::Let {
                let_token, expr, ..
            } => let_token.union(expr.range()),
            ExprPatP::Block {
                open_bracket,
                close_bracket,
                ..
            } => open_bracket.union(*close_bracket),
            ExprPatP::Borrow { borrow_token, expr } => borrow_token.union(expr.range()),
            ExprPatP::Copy { copy_token, expr } => copy_token.union(expr.range()),
            ExprPatP::ConstructData {
                data_constructor,
                close_brace,
                ..
            } => data_constructor.range().union(close_brace.range()),
        }
    }
}