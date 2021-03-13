//! This module contains the mid-level intermediate representation of code.

use std::collections::HashMap;

use quill_common::{
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_parser::NameP;
use quill_type::Type;
use quill_type_deduce::type_check::Pattern;

/// A parsed, type checked, and borrow checked source file.
#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, DefinitionM>,
}

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
pub struct DefinitionM {
    range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<String>,
    pub arg_types: Vec<Type>,
    pub return_type: Type,
    pub cases: Vec<DefinitionCaseM>,
}

impl Ranged for DefinitionM {
    fn range(&self) -> Range {
        self.range
    }
}

#[derive(Debug)]
pub struct DefinitionCaseM {
    range: Range,
    pub arg_patterns: Vec<Pattern>,
    pub replacement: ExpressionM,
}

/// The Expression type is central to the MIR, or mid-level intermediate representation.
/// In an expression in MIR, the type and ownership status of each object is known.
#[derive(Debug)]
pub struct ExpressionM {
    pub ty: Type,
    /// The list of local variables which should be dropped after the execution of this expression.
    ///
    /// All objects in memory should be dropped at some point, otherwise there is a memory leak.
    /// Despite this, forgetting to drop an object is not considered undefined behaviour, it is safe.
    /// It is only possible to directly drop local variables using this in-built drop mechanic.
    /// To drop parts of objects, call the function `drop` on that part of the object; the borrow checker
    /// will then consider this part of the object "moved out".
    pub locals_to_drop: Vec<String>,
    pub contents: ExpressionContentsM,
}

impl Ranged for ExpressionM {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Represents the contents of an expression (which may or may not have been already type checked).
/// The type `T` represents the type variables that we are substituting into this symbol.
/// You should use `ExpressionContents` or `ExpressionContentsT` instead of this enum directly.
#[derive(Debug)]
pub enum ExpressionContentsM {
    /// An argument to this function e.g. `x`.
    Argument(NameP),
    /// A local variable declared by a `lambda` or `let` expression.
    Local(NameP),
    /// A symbol in global scope e.g. `+` or `fold`.
    Symbol {
        /// The name that the symbol refers to.
        name: QualifiedName,
        /// The range where the symbol's name was written in this file.
        range: Range,
        /// The type variables we're substituting into this symbol.
        type_variables: Vec<Type>,
    },
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<ExpressionM>, Box<ExpressionM>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<NameP>,
        expr: Box<ExpressionM>,
    },
    /// A let statement, specifically `let identifier = expr;`.
    Let {
        let_token: Range,
        name: NameP,
        expr: Box<ExpressionM>,
    },
    /// A block of statements, inside parentheses, separated by semicolons,
    /// where the final expression in the block is the type of the block as a whole.
    /// If a semicolon is included as the last token in the block, the block implicitly returns the unit type instead;
    /// in this case, the `final_semicolon` variable contains this semicolon and the block's return type is considered to just be unit.
    Block {
        open_bracket: Range,
        close_bracket: Range,
        statements: Vec<ExpressionM>,
        final_semicolon: Option<Range>,
    },
    /// Explicitly create a value of a data type.
    ConstructData {
        data_type_name: QualifiedName,
        type_ctor: String,
        fields: Vec<(NameP, ExpressionM)>,
        open_brace: Range,
        close_brace: Range,
    },
    /// A raw value, such as a string literal, the `unit` keyword, or an integer literal.
    ImmediateValue {
        value: quill_type_deduce::type_check::ImmediateValue,
        range: Range,
    },
}

impl Ranged for ExpressionContentsM {
    fn range(&self) -> Range {
        match self {
            ExpressionContentsM::Argument(arg) => arg.range,
            ExpressionContentsM::Local(var) => var.range,
            ExpressionContentsM::Symbol { range, .. } => *range,
            ExpressionContentsM::Apply(l, r) => l.range().union(r.range()),
            ExpressionContentsM::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExpressionContentsM::Let {
                let_token, expr, ..
            } => let_token.union(expr.range()),
            ExpressionContentsM::ConstructData {
                open_brace,
                close_brace,
                ..
            } => open_brace.union(*close_brace),
            ExpressionContentsM::Block {
                open_bracket,
                close_bracket,
                ..
            } => open_bracket.union(*close_bracket),
            ExpressionContentsM::ImmediateValue { range, .. } => *range,
        }
    }
}
