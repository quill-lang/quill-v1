mod assumptions;
mod constraints;
mod explicit;
mod generate_constraints;
mod solver;
mod substitute;

use std::collections::BTreeMap;

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged, SourceFileIdentifier},
};
use quill_index::ProjectIndex;
use quill_parser::{expr_pat::ExprPatP, identifier::NameP};
use quill_type::Type;

use crate::{
    hir::expr::{AbstractionVariable, BoundVariable, Expression, ExpressionT},
    index_resolve::as_variable,
    type_check::VisibleNames,
    type_resolve::TypeVariableId,
};

use self::{
    assumptions::Assumptions,
    constraints::{Constraint, ConstraintEqualityReason, Constraints},
};

/// An intermediate result after having documented an expression's types.
#[derive(Debug)]
pub(crate) struct ExprTypeCheck {
    expr: ExpressionT,
    /// When we create a new type variable, we should store its location of definition in this map.
    type_variable_definition_ranges: BTreeMap<TypeVariableId, Range>,
    assumptions: Assumptions,
    constraints: Constraints,
    /// The list of variables defined in `let` statements in scope.
    /// When `generate_constraints` is called, typically the `let_variables` map is simply moved into this field here.
    /// However, if we were generating constraints for a let statement, the let variables list will have this new variable added to it.
    let_variables: BTreeMap<String, AbstractionVariable>,
    /// If this expression was a `let` statement, this will contain a list of all the new variables we defined in this statement,
    new_variables: Option<LetStatementNewVariables>,
}

#[derive(Debug)]
struct LetStatementNewVariables {
    let_token: Range,
    /// A list of the new variables we made, with the type variable we assigned to it.
    new_variables: Vec<(NameP, TypeVariableId)>,
}

pub fn deduce_expr_type(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    args: &BTreeMap<String, BoundVariable>,
    expr: ExprPatP,
    expected_type: Type,
    definition_identifier_range: Range,
) -> DiagnosticResult<Expression> {
    generate_constraints::generate_constraints(
        source_file,
        project_index,
        visible_names,
        args,
        BTreeMap::new(),
        BTreeMap::new(),
        expr,
        None,
    )
    .deny()
    .bind(|mut expr_type_check| {
        if !expr_type_check.assumptions.0.is_empty() {
            panic!("unresolved assumptions {:#?}", expr_type_check.assumptions);
        }
        expr_type_check.constraints.0.push((
            expr_type_check.expr.type_variable.into(),
            Constraint::Equality {
                ty: as_variable(&expected_type),
                reason: ConstraintEqualityReason::ByDefinition {
                    expr: expr_type_check.expr.range(),
                    definition_source: source_file.clone(),
                    definition: definition_identifier_range,
                    high_priority: false,
                },
            },
        ));
        solver::solve_type_constraints(
            source_file,
            project_index,
            expr_type_check.expr,
            expr_type_check.constraints,
            visible_names,
            args,
        )
    })
}
