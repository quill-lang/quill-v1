use std::collections::BTreeMap;

use quill_common::{
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_parser::{
    definition::DefinitionBodyP,
    expr_pat::{ConstantValue, ExprPatP},
    identifier::NameP,
};
use quill_type::{PrimitiveType, Type};

use crate::type_resolve::TypeVariableId;

use super::{definition::Definition, pattern::Pattern};

/// The Expression type is central to the HIR, or high-level intermediate representation.
/// In an expression in HIR, the type of each object is known.
#[derive(Debug)]
pub struct Expression {
    pub ty: Type,
    pub contents: ExpressionContents,
}

impl Ranged for Expression {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Represents the contents of an expression (which may or may not have been already type checked).
/// The type `V` represents the type variables that we are substituting into this symbol.
/// The type `P` represents a pattern.
/// The type `I` represents the contents of an `impl` expression.
/// You should use `ExpressionContents` or `ExpressionContentsT` instead of this enum directly.
#[derive(Debug)]
pub enum ExpressionContentsGeneric<E, T, V, P, I> {
    /// An argument to this function, or a local variable declared by a `lambda` or `let` expression.
    Local(NameP),
    /// A symbol in global scope e.g. `+` or `fold`.
    Symbol {
        /// The name that the symbol refers to.
        name: QualifiedName,
        /// The range where the symbol's name was written in this file.
        range: Range,
        /// The type variables we're substituting into this symbol.
        /// If using an `ExpressionT`, this should be a vector of `TypeVariable`.
        /// If using an `Expression`, this should be a vector of `Type`.
        type_variables: V,
    },
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<E>, Box<E>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<(NameP, T)>,
        expr: Box<E>,
    },
    /// A let statement, specifically `let identifier = expr;`.
    Let {
        let_token: Range,
        name: NameP,
        expr: Box<E>,
    },
    /// A block of statements, inside parentheses, separated by line breaks or commas,
    /// where the final expression in the block is the type of the block as a whole.
    Block {
        open_bracket: Range,
        close_bracket: Range,
        statements: Vec<E>,
    },
    /// Explicitly create a value of a data type.
    ConstructData {
        data_type_name: QualifiedName,
        variant: Option<String>,
        fields: Vec<(NameP, E)>,
        open_brace: Range,
        close_brace: Range,
    },
    /// A raw value, such as a character literal, the `unit` keyword, or an integer literal.
    ConstantValue { value: ConstantValue, range: Range },
    /// A string literal, which will be converted into a cons-list later.
    String { value: String, range: Range },
    /// A borrowed value.
    Borrow { borrow_token: Range, expr: Box<E> },
    /// A copy of a borrowed value.
    Copy { copy_token: Range, expr: Box<E> },
    /// An implementation of an aspect.
    Impl {
        impl_token: Range,
        /// Maps names of definitions to their implementations.
        implementations: I,
    },
    /// A match expression, specifically something of the form `match expr { pat -> result, pat -> result, ... }`
    Match {
        match_token: Range,
        expr: Box<E>,
        /// A list of patterns and their replacements.
        cases: Vec<(P, E)>,
    },
}

/// Represents a case of a definition in an impl expression.
#[derive(Debug)]
pub struct DefinitionCaseGeneric<E> {
    pub range: Range,
    /// WHich definition are we defining a pattern replacement for?
    pub def_name: NameP,
    /// TODO: This should probably be changed to some other pattern type.
    pub arg_patterns: Vec<super::pattern::Pattern>,
    pub replacement: Box<E>,
}

impl<E, T, V, P, I> Ranged for ExpressionContentsGeneric<E, T, V, P, I>
where
    E: Ranged,
{
    fn range(&self) -> Range {
        match self {
            ExpressionContentsGeneric::Local(var) => var.range,
            ExpressionContentsGeneric::Symbol { range, .. } => *range,
            ExpressionContentsGeneric::Apply(l, r) => l.range().union(r.range()),
            ExpressionContentsGeneric::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExpressionContentsGeneric::Let {
                let_token, expr, ..
            } => let_token.union(expr.range()),
            ExpressionContentsGeneric::ConstructData {
                open_brace,
                close_brace,
                ..
            } => open_brace.union(*close_brace),
            ExpressionContentsGeneric::Block {
                open_bracket,
                close_bracket,
                ..
            } => open_bracket.union(*close_bracket),
            ExpressionContentsGeneric::ConstantValue { range, .. } => *range,
            ExpressionContentsGeneric::String { range, .. } => *range,
            ExpressionContentsGeneric::Borrow {
                borrow_token, expr, ..
            } => borrow_token.union(expr.range()),
            ExpressionContentsGeneric::Copy {
                copy_token, expr, ..
            } => copy_token.union(expr.range()),
            ExpressionContentsGeneric::Impl { impl_token, .. } => *impl_token,
            ExpressionContentsGeneric::Match { match_token, .. } => *match_token,
        }
    }
}

pub type ExpressionContents =
    ExpressionContentsGeneric<Expression, Type, Vec<Type>, Pattern, BTreeMap<String, Definition>>;
pub type ExpressionContentsT = ExpressionContentsGeneric<
    ExpressionT,
    TypeVariable,
    BTreeMap<String, TypeVariable>,
    ExprPatP,
    DefinitionBodyP,
>;

/// A variable bound by the definition of a function.
#[derive(Debug, Clone)]
pub struct BoundVariable {
    pub range: Range,
    pub var_type: Type,
}

/// A variable bound by some abstraction e.g. a lambda or a let inside it.
#[derive(Debug, Clone)]
pub struct AbstractionVariable {
    pub range: Range,
    pub var_type: TypeVariableId,
}

#[derive(Debug)]
pub struct ExpressionT {
    pub type_variable: TypeVariableId,
    pub contents: ExpressionContentsT,
    /// If this expression was instanced explicitly, the @ token is given here.
    /// This makes sure that the type variable is never a function where its first argument is an impl.
    pub explicit_token: Option<Range>,
}

impl Ranged for ExpressionT {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Closely tied to the `Type` struct, this is used while type checking to allow
/// unknown types, represented by `TypeVariableId`s.
#[derive(Debug, Clone)]
pub enum TypeVariable {
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either[T, U]`.
    Named {
        name: QualifiedName,
        parameters: Vec<TypeVariable>,
    },
    Function(Box<TypeVariable>, Box<TypeVariable>),
    /// A known type variable, e.g. `T` or `F[A]`.
    Variable {
        variable: String,
        parameters: Vec<TypeVariable>,
    },
    /// A completely unknown type - we don't even have a type variable letter to describe it such as `T`.
    /// These are assigned random IDs, and when printed are converted into Greek letters using the
    /// `TypeVariablePrinter`.
    Unknown {
        id: TypeVariableId,
    },
    /// A primitive type, built in to the core of the type system.
    Primitive(PrimitiveType),
    /// Borrow conditions are checked later.
    Borrow {
        ty: Box<TypeVariable>,
    },
    /// An explicitly named implementation of an aspect possibly with type parameters.
    Impl {
        name: QualifiedName,
        parameters: Vec<TypeVariable>,
    },
}
