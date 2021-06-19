use quill_common::location::Range;

use crate::{expr_pat::ExprPatP, identifier::NameP, types::TypeP, visibility::Visibility};

/// A `def` block. Defines a symbol's type and what values it takes under what circumstances.
#[derive(Debug)]
pub struct DefinitionP {
    pub vis: Visibility,
    pub name: NameP,
    /// This definition might be defined with certain quantified type variables, e.g. foo[A, B].
    pub type_parameters: Vec<TypeParameterP>,
    pub definition_type: TypeP,
    pub body: DefinitionBodyP,
}

#[derive(Debug)]
pub enum DefinitionBodyP {
    /// The body is defined as a series of cases to be pattern matched against.
    PatternMatch(Vec<DefinitionCaseP>),
    /// The body of the function is not written in Quill, it is an intrinsic and will be replaced
    /// by hand-written LLVM IR code.
    CompilerIntrinsic(Range),
}

/// Represents the loan conditions of a borrowed value.
#[derive(Debug, Clone)]
pub struct TypeBorrowP {
    pub borrow_token: Range,
    pub lifetime: LifetimeP,
}

/// Either the definition or use of a lifetime parameter.
#[derive(Debug, Clone)]
pub struct LifetimeP {
    pub name: NameP,
}

#[derive(Debug, Clone)]
pub struct TypeParameterP {
    pub name: NameP,
    /// A type variable may have one or more unnamed parameters, e.g. `F[_]` is a common type for a functor.
    /// This field stores how many such parameters the type variable has.
    pub parameters: u32,
}

/// Represents a case in a definition where we can replace the left hand side of a pattern with the right hand side.
#[derive(Debug)]
pub struct DefinitionCaseP {
    pub pattern: ExprPatP,
    pub replacement: ExprPatP,
}
