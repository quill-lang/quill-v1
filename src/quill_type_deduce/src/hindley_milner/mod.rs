mod assumptions;
mod constraints;
mod explicit;
mod generate_constraints;
mod solver;
mod substitute;

pub(crate) use substitute::VisibleLocalNames;

use std::collections::BTreeMap;

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged, SourceFileIdentifier},
};
use quill_index::ProjectIndex;
use quill_parser::{expr_pat::ExprPatP, identifier::NameP};
use quill_type::Type;

use crate::{
    hir::expr::{AbstractionVariable, BoundVariable, Expression, ExpressionT, TypeVariable},
    index_resolve::{as_variable, instantiate},
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

/// The list of `visible_local_names` is used for inner type deduction.
/// Type deduction of impls is done in a separate step, so we need to use this list to access the types of outer local variables.
/// This holds the types of outer local variables, including the arguments to the function.
pub(crate) fn deduce_expr_type(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    visible_names: &VisibleNames,
    visible_local_names: &VisibleLocalNames,
    args: &BTreeMap<String, BoundVariable>,
    expr: ExprPatP,
    expected_type: Type,
    definition_identifier_range: Range,
) -> DiagnosticResult<Expression> {
    let mut extra_constraints = BTreeMap::new();
    // Pretend that the visible local names provided were given using `let` statements, just for type deduction to work.
    generate_constraints::generate_constraints(
        source_file,
        project_index,
        visible_names,
        args,
        BTreeMap::new(),
        visible_local_names
            .iter()
            .map(|(name, local)| {
                let tvid = TypeVariableId::default();
                extra_constraints.insert(name, (tvid, &local.ty));
                (
                    name.name.clone(),
                    AbstractionVariable {
                        range: name.range,
                        var_type: tvid,
                    },
                )
            })
            .collect(),
        expr,
        None,
    )
    .deny()
    .bind(|mut expr_type_check| {
        for (variable_name, (type_variable_id, expected_type)) in extra_constraints {
            let let_assumptions = expr_type_check
                .assumptions
                .0
                .remove(variable_name)
                .unwrap_or_else(Vec::new);

            for assumption in let_assumptions {
                expr_type_check.constraints.0.push((
                    TypeVariable::Unknown { id: assumption.0 },
                    Constraint::Equality {
                        ty: TypeVariable::Unknown {
                            id: type_variable_id,
                        },
                        reason: ConstraintEqualityReason::ByDefinition {
                            expr: variable_name.range,
                            definition_source: source_file.clone(),
                            definition: variable_name.range,
                            high_priority: true,
                        },
                    },
                ));
            }
            expr_type_check.constraints.0.push((
                TypeVariable::Unknown {
                    id: type_variable_id,
                },
                Constraint::Equality {
                    ty: instantiate(expected_type).result,
                    reason: ConstraintEqualityReason::ByDefinition {
                        expr: variable_name.range,
                        definition_source: source_file.clone(),
                        definition: variable_name.range,
                        high_priority: true,
                    },
                },
            ))
        }

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
