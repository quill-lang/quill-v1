use std::collections::{hash_map::Entry, HashMap, VecDeque};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
};
use quill_index::ProjectIndex;

use crate::{
    hir::expr::{Expression, ExpressionT, TypeVariable},
    type_check::TypeVariablePrinter,
    type_resolve::TypeVariableId,
};

use super::{
    constraints::{Constraint, ConstraintEqualityReason, Constraints},
    substitute,
};

/// Deduces the type of an expression.
/// Any error messages are added to the diagnostic result.
///
/// This mostly implements the algorithm from Generalizing Hindley-Milner Type Inference Algorithms (2002)
/// <https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.18.9348>.
pub(crate) fn solve_type_constraints(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    expr: ExpressionT,
    constraints: Constraints,
) -> DiagnosticResult<Expression> {
    // println!("Deducing type of {:#?}", expr);
    // println!("Constraints: {:#?}", constraints);

    // We implement the `SOLVE` algorithm from the above paper.
    // The substitutions are defined to be idempotent, so a map instead of an ordered vec shall suffice.

    let mut high_priority_constraints = VecDeque::new();
    let mut mid_priority_constraints = VecDeque::new();
    let mut low_priority_constraints = VecDeque::new();
    for constraint in constraints.0 {
        match &constraint.1 {
            Constraint::Equality { reason, .. } => match reason {
                ConstraintEqualityReason::LambdaType { .. } => {
                    high_priority_constraints.push_back(constraint)
                }
                ConstraintEqualityReason::ByDefinition { .. } => {
                    low_priority_constraints.push_back(constraint)
                }
                _ => mid_priority_constraints.push_back(constraint),
            },
        }
    }
    // To solve the constraints, we will pop entries off the front of the queue, process them, and if needed push them to the back of the queue.
    // There are a few phases to solving constraints - there are a number of constraints we want to process either first or last.
    // We'll start by supplying the empty substitution.
    solve_type_constraint_queue(
        source_file,
        project_index,
        high_priority_constraints,
        HashMap::<TypeVariableId, TypeVariable>::new(),
    )
    .bind(|substitution| {
        solve_type_constraint_queue(
            source_file,
            project_index,
            mid_priority_constraints,
            substitution,
        )
    })
    .bind(|substitution| {
        solve_type_constraint_queue(
            source_file,
            project_index,
            low_priority_constraints,
            substitution,
        )
    })
    .bind(|substitution| {
        // println!("Sub was:");
        // println!("{:#?}", substitution);
        substitute::substitute(&substitution, expr, source_file)
    })
}

fn solve_type_constraint_queue(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    mut constraint_queue: VecDeque<(TypeVariable, Constraint)>,
    mut substitution: HashMap<TypeVariableId, TypeVariable>,
) -> DiagnosticResult<HashMap<TypeVariableId, TypeVariable>> {
    //dbg!(&constraint_queue);
    while let Some((type_variable, constraint)) = constraint_queue.pop_front() {
        // println!(
        //     "Solving constraint {:#?} => {:#?}",
        //     type_variable, constraint
        // );
        match constraint {
            Constraint::Equality { ty: other, reason } => {
                // This constraint specifies that `type_variable === other`.
                // So we'll find the most general unifier between the two types.
                match most_general_unifier(project_index, other.clone(), type_variable.clone()) {
                    Ok(mgu) => {
                        // Add this substitution to the list of substitutions,
                        // and also apply the substitution to the current list of constraints.
                        apply_substitution_to_constraints(&mgu, &mut constraint_queue);
                        match unify(project_index, substitution.clone(), mgu) {
                            Ok(sub) => {
                                substitution = sub;

                                // Check to make sure we haven't introduced an infinite type.
                                if let Err(error) = fix_infinite_type(&mut substitution) {
                                    return DiagnosticResult::fail(process_infinite_type_error(
                                        source_file,
                                        error,
                                        reason,
                                        substitution,
                                    ));
                                }
                            }
                            Err(error) => {
                                return DiagnosticResult::fail(process_unification_error(
                                    source_file,
                                    error,
                                    reason,
                                    substitution,
                                ));
                            }
                        }
                    }
                    Err(error) => {
                        return DiagnosticResult::fail(process_unification_error(
                            source_file,
                            error,
                            reason,
                            substitution,
                        ));
                    }
                }
            }
        }
    }

    DiagnosticResult::ok(substitution)
}

struct InfiniteTypeError {
    erroneous_substitutions: Vec<(TypeVariableId, TypeVariable)>,
}

/// Check to see if we've created an infinite type e.g. a ~ [a]. This is invariably an error.
/// If an infinite type was found, the substitution referencing it is removed from the substitution,
/// so that error messages do not stack overflow trying to print the infinite type.
fn fix_infinite_type(
    substitution: &mut HashMap<TypeVariableId, TypeVariable>,
) -> Result<(), InfiniteTypeError> {
    let mut to_remove = Vec::new();
    for (k, v) in substitution.iter() {
        if contains_id(v, k) {
            to_remove.push(*k);
        }
    }
    let erroneous_substitutions = to_remove
        .iter()
        .map(|k| substitution.remove_entry(k).unwrap())
        .filter(|(substitution_id, substitution_replacement)| {
            // Check if the constraint simply maps a type to itself.
            // This is a valid deduction, but must be removed since it results in an infinite loop.
            if let TypeVariable::Unknown {
                id: substitution_replacement_id,
            } = substitution_replacement
            {
                substitution_replacement_id != substitution_id
            } else {
                true
            }
        })
        .collect::<Vec<_>>();

    if erroneous_substitutions.is_empty() {
        Ok(())
    } else {
        Err(InfiniteTypeError {
            erroneous_substitutions,
        })
    }
}

/// Does the given type variable reference the given ID?
fn contains_id(v: &TypeVariable, id: &TypeVariableId) -> bool {
    match v {
        TypeVariable::Named { parameters, .. } => parameters.iter().any(|p| contains_id(p, id)),
        TypeVariable::Function(l, r) => contains_id(l, id) || contains_id(r, id),
        TypeVariable::Variable { parameters, .. } => parameters.iter().any(|v| contains_id(v, id)),
        TypeVariable::Unknown { id: other_id } => other_id == id,
        TypeVariable::Primitive(_) => false,
        TypeVariable::Borrow { ty, .. } => contains_id(&*ty, id),
    }
}

/// Returns the range that we should raise the error at, and a list of help/note messages relating to the exact constraint that was violated.
fn process_constraint_reason(
    source_file: &SourceFileIdentifier,
    ty_printer: &mut TypeVariablePrinter,
    reason: ConstraintEqualityReason,
) -> (Range, Vec<HelpMessage>) {
    // TODO make these error messages. It'll be better to make the messages
    // once we know what kinds of scenarios trigger them after we experiment more.
    match reason {
        ConstraintEqualityReason::Apply {
            function_range,
            function_ty,
            argument_range,
            argument_ty,
        } => {
            let messages = vec![
                HelpMessage {
                    message: format!(
                        "error was raised because we tried to apply this function of type {}...",
                        ty_printer.print(function_ty),
                    ),
                    help_type: HelpType::Note,
                    diagnostic: Diagnostic::at(source_file, &function_range),
                },
                HelpMessage {
                    message: format!(
                        "...to an argument of type {}",
                        ty_printer.print(argument_ty)
                    ),
                    help_type: HelpType::Note,
                    diagnostic: Diagnostic::at(source_file, &argument_range),
                },
            ];
            (function_range, messages)
        }
        ConstraintEqualityReason::ByDefinition { expr, definition } => {
            let messages = vec![HelpMessage {
                message: String::from(
                    "error was raised because this expression's type was defined here",
                ),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, &definition),
            }];
            (expr, messages)
        }
        ConstraintEqualityReason::LambdaParameter {
            lambda,
            param_name,
            param_range,
        } => {
            let messages = vec![HelpMessage {
                message: format!(
                    "error was raised because of the use of the lambda parameter {} inside the body of the lambda expression",
                    param_name,
                ),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, &param_range),
            }];
            (lambda, messages)
        }
        ConstraintEqualityReason::InstanceLet {
            variable_name,
            variable_type,
            expr,
            let_token,
        } => {
            let messages = vec![HelpMessage {
                message: format!(
                    "error was raised because of the use of the variable {} which has type {}",
                    variable_name,
                    ty_printer.print(variable_type)
                ),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, &let_token),
            }];
            (expr, messages)
        }
        ConstraintEqualityReason::Field {
            expr,
            data_type,
            field,
            ..
        } => {
            let messages = vec![HelpMessage {
                message: format!(
                    "error was raised because of the use of this expression in field {} of data type {}",
                    field,
                    data_type,
                ),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, &expr),
            }];
            (expr, messages)
        }
        _ => {
            panic!("Could not print error message reason {:#?}", reason);
        }
    }
}

fn process_infinite_type_error(
    source_file: &SourceFileIdentifier,
    error: InfiniteTypeError,
    reason: ConstraintEqualityReason,
    substitution: HashMap<TypeVariableId, TypeVariable>,
) -> ErrorMessage {
    let mut ty_printer = TypeVariablePrinter::new(substitution);

    let (error_range, help) = process_constraint_reason(source_file, &mut ty_printer, reason);

    ErrorMessage::new_with_many(
        format!(
            "a self-referential type {} ~ {} was created",
            ty_printer.print(TypeVariable::Unknown {
                id: error.erroneous_substitutions[0].0,
            }),
            ty_printer.print(error.erroneous_substitutions[0].1.clone()),
        ),
        Severity::Error,
        Diagnostic::at(source_file, &error_range),
        help,
    )
}

/// Process an error message generated by computing the most general unifier for two types.
fn process_unification_error(
    source_file: &SourceFileIdentifier,
    error: UnificationError,
    reason: ConstraintEqualityReason,
    substitution: HashMap<TypeVariableId, TypeVariable>,
) -> ErrorMessage {
    let mut ty_printer = TypeVariablePrinter::new(substitution);

    // The constraint reasons we made earlier will help us emit an error.
    let (error_range, help) = process_constraint_reason(source_file, &mut ty_printer, reason);

    // Now emit the error.
    match error {
        UnificationError::VariableNameMismatch { name, other_name } => ErrorMessage::new_with_many(
            format!("type variables {} and {} did not match", name, other_name,),
            Severity::Error,
            Diagnostic::at(source_file, &error_range),
            help,
        ),
        UnificationError::ExpectedDifferent { expected, actual } => ErrorMessage::new_with_many(
            format!(
                "expected type {}, but found type {}",
                ty_printer.print(expected),
                ty_printer.print(actual)
            ),
            Severity::Error,
            Diagnostic::at(source_file, &error_range),
            help,
        ),
        UnificationError::ExpectedVariable { actual, variable } => ErrorMessage::new_with_many(
            format!(
                "a data type {} was found, but it was expected to be the type variable {}",
                ty_printer.print(actual),
                variable,
            ),
            Severity::Error,
            Diagnostic::at(source_file, &error_range),
            help,
        ),
    }
}

fn apply_substitution_to_constraints(
    mgu: &HashMap<TypeVariableId, TypeVariable>,
    constraint_queue: &mut VecDeque<(TypeVariable, Constraint)>,
) {
    for (ty, constraint) in constraint_queue {
        apply_substitution(mgu, ty);
        match constraint {
            Constraint::Equality { ty: other, .. } => apply_substitution(mgu, other),
        }
    }
}

fn apply_substitution(sub: &HashMap<TypeVariableId, TypeVariable>, ty: &mut TypeVariable) {
    if let TypeVariable::Unknown { id } = ty {
        if let Some(sub_value) = sub.get(id) {
            *ty = sub_value.clone();
        }
    }
}

enum UnificationError {
    /// We expected a certain type, but we actually got a different type.
    ExpectedDifferent {
        expected: TypeVariable,
        actual: TypeVariable,
    },
    /// An expression was found to be of the type of two distinct variables.
    VariableNameMismatch { name: String, other_name: String },
    /// One type was a named data type, the other type was a type variable quantified in the function signature.
    ExpectedVariable {
        actual: TypeVariable,
        variable: String,
    },
}

/// Returns a substitution which unifies the two types. If one could not be found, this is a type error, and None will be returned.
fn most_general_unifier(
    project_index: &ProjectIndex,
    expected: TypeVariable,
    actual: TypeVariable,
) -> Result<HashMap<TypeVariableId, TypeVariable>, UnificationError> {
    // If one of them is an unknown type variable, just set it to the other one.
    match expected {
        TypeVariable::Named {
            name: left_name,
            parameters: left_parameters,
        } => {
            match actual {
                TypeVariable::Named {
                    name: right_name,
                    parameters: right_parameters,
                } => {
                    // Both type variables are named types.
                    // Check that they are the same.
                    if left_name == right_name {
                        // Unify the type parameters.
                        // The lists must have equal length, since the names matched.
                        let mut mgu = HashMap::new();
                        for (left_param, right_param) in
                            left_parameters.into_iter().zip(right_parameters)
                        {
                            let inner_mgu =
                                most_general_unifier(project_index, left_param, right_param)?;
                            mgu = unify(project_index, mgu, inner_mgu)?;
                        }
                        Ok(mgu)
                    } else {
                        Err(UnificationError::ExpectedDifferent {
                            expected: TypeVariable::Named {
                                name: left_name,
                                parameters: left_parameters,
                            },
                            actual: TypeVariable::Named {
                                name: right_name,
                                parameters: right_parameters,
                            },
                        })
                    }
                }
                TypeVariable::Unknown { id: right } => {
                    let mut map = HashMap::new();
                    map.insert(
                        right,
                        TypeVariable::Named {
                            name: left_name,
                            parameters: left_parameters,
                        },
                    );
                    Ok(map)
                }
                TypeVariable::Function(right_param, right_result) => {
                    Err(UnificationError::ExpectedDifferent {
                        expected: TypeVariable::Named {
                            name: left_name,
                            parameters: left_parameters,
                        },
                        actual: TypeVariable::Function(right_param, right_result),
                    })
                }
                TypeVariable::Variable { variable, .. } => {
                    Err(UnificationError::ExpectedVariable {
                        actual: TypeVariable::Named {
                            name: left_name,
                            parameters: left_parameters,
                        },
                        variable,
                    })
                }
                actual => Err(UnificationError::ExpectedDifferent {
                    expected: TypeVariable::Named {
                        name: left_name,
                        parameters: left_parameters,
                    },
                    actual,
                }),
            }
        }
        TypeVariable::Unknown { id } => {
            let mut map = HashMap::new();
            map.insert(id, actual);
            Ok(map)
        }
        TypeVariable::Function(left_param, left_result) => {
            match actual {
                TypeVariable::Function(right_param, right_result) => {
                    // Both were functions. Unify both the parameters and the results.
                    let mgu1 = most_general_unifier(project_index, *left_param, *right_param)?;
                    let mgu2 = most_general_unifier(project_index, *left_result, *right_result)?;
                    unify(project_index, mgu1, mgu2)
                }
                TypeVariable::Unknown { id: right } => {
                    let mut map = HashMap::new();
                    map.insert(right, TypeVariable::Function(left_param, left_result));
                    Ok(map)
                }
                TypeVariable::Variable { variable, .. } => {
                    Err(UnificationError::ExpectedVariable {
                        actual: TypeVariable::Function(left_param, left_result),
                        variable,
                    })
                }
                actual => Err(UnificationError::ExpectedDifferent {
                    expected: TypeVariable::Function(left_param, left_result),
                    actual,
                }),
            }
        }
        TypeVariable::Variable {
            variable,
            parameters: left_parameters,
        } => match actual {
            TypeVariable::Variable {
                variable: other_variable,
                ..
            } => {
                if other_variable == variable {
                    Ok(HashMap::new())
                } else {
                    Err(UnificationError::VariableNameMismatch {
                        name: variable,
                        other_name: other_variable,
                    })
                }
            }
            TypeVariable::Unknown { id: right } => {
                let mut map = HashMap::new();
                map.insert(
                    right,
                    TypeVariable::Variable {
                        variable,
                        parameters: left_parameters,
                    },
                );
                Ok(map)
            }
            actual => Err(UnificationError::ExpectedVariable { actual, variable }),
        },
        TypeVariable::Primitive(prim) => match actual {
            TypeVariable::Unknown { id } => {
                let mut map = HashMap::new();
                map.insert(id, TypeVariable::Primitive(prim));
                Ok(map)
            }
            TypeVariable::Primitive(actual) => {
                if prim == actual {
                    Ok(HashMap::new())
                } else {
                    Err(UnificationError::ExpectedDifferent {
                        expected: TypeVariable::Primitive(prim),
                        actual: TypeVariable::Primitive(actual),
                    })
                }
            }
            actual => Err(UnificationError::ExpectedDifferent {
                expected: TypeVariable::Primitive(prim),
                actual,
            }),
        },
        TypeVariable::Borrow { ty } => match actual {
            TypeVariable::Unknown { id } => {
                let mut map = HashMap::new();
                map.insert(id, TypeVariable::Borrow { ty });
                Ok(map)
            }
            TypeVariable::Borrow { ty: other_ty } => {
                most_general_unifier(project_index, *ty, *other_ty)
            }
            actual => Err(UnificationError::ExpectedDifferent {
                expected: TypeVariable::Borrow { ty },
                actual,
            }),
        },
    }
}

fn unify(
    project_index: &ProjectIndex,
    mut a: HashMap<TypeVariableId, TypeVariable>,
    b: HashMap<TypeVariableId, TypeVariable>,
) -> Result<HashMap<TypeVariableId, TypeVariable>, UnificationError> {
    for (id, v) in b {
        match a.entry(id) {
            Entry::Occupied(occupied) => {
                let inner_mgu = most_general_unifier(project_index, v, occupied.get().clone())?;
                a = unify(project_index, a, inner_mgu)?;
            }
            Entry::Vacant(vacant) => {
                vacant.insert(v);
            }
        }
    }
    Ok(a)
}
