//! Creates the MIR code that performs a pattern matching operation.

use std::collections::HashMap;

use multimap::MultiMap;
use quill_common::{
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_parser::{expr_pat::ConstantValue, identifier::NameP};
use quill_type::Type;
use quill_type_deduce::{hir::pattern::Pattern, replace_type_variables, TypeConstructorInvocation};

use crate::{definition::DefinitionTranslationContext, mir::*};

#[derive(Debug)]
struct PatternMismatch {
    place: Place,
    reason: PatternMismatchReason,
}

#[derive(Debug)]
enum PatternMismatchReason {
    EnumDiscriminant {
        /// What was the name of the enum we want to pattern match?
        enum_name: QualifiedName,
        enum_parameters: Vec<Type>,
        /// Maps enum discriminant names to the indices of the patterns that are matched by this discriminant.
        /// If a case is valid for any discriminant, it is put in *every* case.
        cases: MultiMap<String, usize>,
    },
    Constant {
        /// Maps constant values to the indices of the patterns that are matched by this discriminant.
        /// If a case is valid for any value, it is put in *every* case, and also the `default` list.
        cases: MultiMap<ConstantValue, usize>,
        default: Vec<usize>,
    },
}

/// Given a list of patterns, in which place do they first (pairwise) differ, and how? If they do not differ, return None.
/// Two patterns are said to differ in a place if a different primitive value or enum variant at this place
/// could cause exactly one pattern to match.
/// `var` is the place where the variable that we will match is stored.
fn first_difference(
    project_index: &ProjectIndex,
    var: Place,
    ty: Type,
    patterns: &[Pattern],
) -> Option<PatternMismatch> {
    // Check to see what type the patterns represent.
    // Even though we already know `ty`, we do this check to see whether the *patterns* care
    // about what type it is.
    let type_name = patterns.iter().find_map(|pat| {
        if let Pattern::TypeConstructor { type_ctor, .. } = pat {
            Some(type_ctor.data_type.clone())
        } else {
            None
        }
    });

    if type_name.is_some() {
        // At least one of the patterns wants to inspect this variable, either its fields or its enum variant.
        // Check to see if the patterns represent an enum.
        let is_enum = patterns.iter().any(|pat| {
            if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                type_ctor.variant.is_some()
            } else {
                false
            }
        });

        let need_to_switch_enum = if is_enum {
            // Because (at least) one pattern referenced an enum variant, we might need to switch on this enum's discriminant.
            // In particular, if two patterns reference *different* variants, or one does *not* reference a variant,
            // then we need to switch the discriminant.
            // Sometimes this function can be called with a non-exhaustive set of patterns, if we've already excluded
            // some previous patterns. This means that it's possible that an enum variant is referenced, but we already know
            // which variant it is (we've already ruled out all other patterns).
            let mut expected_variant = None;
            let mut found_mismatch = false;
            for pat in patterns.iter() {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    if let Some(the_expected_variant) = expected_variant.take() {
                        if the_expected_variant != type_ctor.variant.as_ref().unwrap() {
                            // Two enum patterns referenced a different variant.
                            // So we need to switch on the enum discriminant.
                            found_mismatch = true;
                            break;
                        }
                    } else {
                        expected_variant = Some(type_ctor.variant.as_ref().unwrap());
                    }
                } else {
                    found_mismatch = true;
                    break;
                }
            }
            found_mismatch
        } else {
            false
        };

        if need_to_switch_enum {
            // Let's store which patterns require which discriminants.
            // First, work out the list of all discriminants for this enum.

            let (enum_name, enum_parameters) = if let Type::Named { name, parameters } = ty {
                (name, parameters)
            } else {
                unreachable!()
            };

            let all_variants = if let TypeDeclarationTypeI::Enum(enumi) =
                &project_index[&enum_name.source_file].types[&enum_name.name].decl_type
            {
                enumi
                    .variants
                    .iter()
                    .map(|variant| variant.name.name.clone())
                    .collect::<Vec<_>>()
            } else {
                unreachable!()
            };

            let mut cases = MultiMap::new();

            for (i, pat) in patterns.iter().enumerate() {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    // This case applies to exactly one discriminant.
                    cases.insert(type_ctor.variant.as_ref().unwrap().clone(), i);
                } else {
                    // This case applies to all discriminants.
                    for variant in &all_variants {
                        cases.insert(variant.clone(), i);
                    }
                }
            }

            Some(PatternMismatch {
                place: var,
                reason: PatternMismatchReason::EnumDiscriminant {
                    enum_name,
                    enum_parameters,
                    cases,
                },
            })
        } else {
            // We do not need to match on the enum discriminator, so we now want to consider the first difference *inside* each pattern.
            // We check each field in the data type, and consider how (and if) the patterns differ when reasoning about this field.

            // Note that in this branch, all cases must have the same enum variant (if this is an enum, not a data type).
            // So let's work out which variant of the enum it is.
            let enum_variant = patterns.iter().find_map(|pat| {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    type_ctor.variant.clone()
                } else {
                    None
                }
            });

            let fields = patterns
                .iter()
                .find_map(|pat| {
                    if let Pattern::TypeConstructor { fields, .. } = pat {
                        Some(
                            fields
                                .iter()
                                .map(|(name, ty, _pat)| (name.name.clone(), ty.clone()))
                                .collect::<Vec<_>>(),
                        )
                    } else {
                        None
                    }
                })
                .unwrap();

            for (field_name, field_ty) in fields {
                // Do the patterns differ in this field?
                // First, let's store the pattern that each case provides for each field.
                // If the pattern was `_` or named (e.g. `a`), then the field is not matched;
                // in this case we assume that the field's pattern is `_`.
                let field_patterns = patterns
                    .iter()
                    .map(|pat| {
                        if let Pattern::TypeConstructor { fields, .. } = pat {
                            fields
                                .iter()
                                .find_map(|(inner_field_name, _, inner_field_pat)| {
                                    if inner_field_name.name == field_name {
                                        Some(inner_field_pat.clone())
                                    } else {
                                        None
                                    }
                                })
                                .unwrap()
                        } else {
                            Pattern::Unknown(pat.range())
                        }
                    })
                    .collect::<Vec<_>>();

                // Now, check whether the field patterns differ.
                if let Some(diff) = first_difference(
                    project_index,
                    var.clone()
                        .then(if let Some(variant) = enum_variant.clone() {
                            PlaceSegment::EnumField {
                                variant,
                                field: field_name,
                            }
                        } else {
                            PlaceSegment::DataField { field: field_name }
                        }),
                    field_ty,
                    &field_patterns,
                ) {
                    return Some(diff);
                }
            }

            // The patterns all matched, since we've checked each field and we didn't find a mismatch.
            None
        }
    } else {
        // No patterns are probing inside this variable.
        // Now, check if any pattern is a primitive constant.
        let immediate_value = patterns.iter().find_map(|pat| {
            if let Pattern::Constant { value, .. } = pat {
                if !matches!(value, ConstantValue::Unit) {
                    Some(*value)
                } else {
                    None
                }
            } else {
                None
            }
        });

        if let Some(immediate_value) = immediate_value {
            // We may need to switch on this value.
            let needs_switch = patterns.iter().any(|pat| {
                if let Pattern::Constant { value, .. } = pat {
                    *value != immediate_value
                } else {
                    true
                }
            });

            if needs_switch {
                // There was a mismatch. We need to switch on this value.
                let mut cases = MultiMap::new();
                let mut default = Vec::new();

                for (i, pat) in patterns.iter().enumerate() {
                    if let Pattern::Constant { value, .. } = pat {
                        // This case applies to exactly one value.
                        cases.insert(*value, i);
                    } else {
                        // This case applies to all values.
                        default.push(i);
                    }
                }

                // Add default values to all cases.
                let keys = cases.keys().copied().collect::<Vec<_>>();
                for item in &default {
                    for value in &keys {
                        cases.insert(*value, *item);
                    }
                }

                Some(PatternMismatch {
                    place: var,
                    reason: PatternMismatchReason::Constant { cases, default },
                })
            } else {
                // The variable's value was referenced,
                // but no switch was required since all branches required the same value.
                None
            }
        } else {
            // The patterns did not reference an immediate value. No mismatch was detected.
            None
        }
    }
}

/// Given a list of patterns for a function, in which place do they first (pairwise) differ, and how?
/// If they do not differ, return None. Any `Place` returned will be relative to an argument.
fn first_difference_function(
    project_index: &ProjectIndex,
    arg_types: Vec<Type>,
    patterns: &[Vec<Pattern>],
) -> Option<PatternMismatch> {
    for i in 0..arg_types.len() {
        let arg_patterns = patterns
            .iter()
            .map(|vec| vec[i].clone())
            .collect::<Vec<_>>();
        if let Some(diff) = first_difference(
            project_index,
            Place::new(LocalVariableName::Argument(ArgumentIndex(i as u64))),
            arg_types[i].clone(),
            &arg_patterns,
        ) {
            return Some(diff);
        }
    }
    None
}

/// `arg_patterns` represents some patterns for the arguments of a function.
/// If any of these reference the given place, replace the pattern with the given replacement.
/// This allows us to constrain `_` or named patterns to the known variant
/// after we've switched on the discriminant, so that we don't get infinite recursion.
fn reference_place_function(
    place: Place,
    replacement: Pattern,
    mut arg_patterns: Vec<Pattern>,
) -> Vec<Pattern> {
    let i = if let LocalVariableName::Argument(ArgumentIndex(i)) = place.local {
        i as usize
    } else {
        unreachable!();
    };

    arg_patterns[i] = reference_place(place.projection, replacement, arg_patterns[i].clone());
    arg_patterns
}

/// If this pattern references the given place relative to the root of the pattern,
/// replace the pattern the given replacement.
fn reference_place(
    mut place_segments: Vec<PlaceSegment>,
    replacement: Pattern,
    pattern: Pattern,
) -> Pattern {
    if place_segments.is_empty() {
        // Check if this pattern is "named" or "unknown". If so, replace it with the replacement.
        let should_replace = match pattern {
            Pattern::Named(_) => true,
            Pattern::Constant { .. } => false,
            Pattern::TypeConstructor { .. } => false,
            Pattern::Impl { .. } => false,
            Pattern::Function { .. } => unreachable!(),
            Pattern::Unknown(_) => true,
        };

        if should_replace {
            replacement
        } else {
            pattern
        }
    } else {
        let segment = place_segments.remove(0);
        match segment {
            PlaceSegment::DataField { field } => {
                if let Pattern::TypeConstructor {
                    type_ctor,
                    mut fields,
                } = pattern
                {
                    for (field_name, _field_type, field_pat) in &mut fields {
                        if field_name.name == field {
                            *field_pat =
                                reference_place(place_segments, replacement, field_pat.clone());
                            break;
                        }
                    }
                    Pattern::TypeConstructor { type_ctor, fields }
                } else {
                    pattern
                }
            }
            PlaceSegment::EnumField { field, .. } => {
                if let Pattern::TypeConstructor {
                    type_ctor,
                    mut fields,
                } = pattern
                {
                    for (field_name, _field_type, field_pat) in &mut fields {
                        if field_name.name == field {
                            *field_pat =
                                reference_place(place_segments, replacement, field_pat.clone());
                            break;
                        }
                    }
                    Pattern::TypeConstructor { type_ctor, fields }
                } else {
                    pattern
                }
            }
            PlaceSegment::EnumDiscriminant => Pattern::Unknown(pattern.range()),
            PlaceSegment::ImplField { .. } => Pattern::Unknown(pattern.range()),
        }
    }
}

/// Creates a basic block (or tree of basic blocks) that
/// performs the given pattern matching operation for an entire function body.
/// The value is matched against each case, and basic blocks are created that branch to
/// these 'case' blocks when the pattern is matched. The return value is a basic block
/// which will perform this match operation, then jump to the case blocks.
pub(crate) fn perform_match_function(
    project_index: &ProjectIndex,
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    arg_types: Vec<Type>,
    cases: Vec<(Vec<Pattern>, BasicBlockId)>,
) -> BasicBlockId {
    // Recursively find the first difference between patterns, until each case has its own branch.
    // println!("Cases: {:#?}", cases);
    let (patterns, blocks): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    if let Some(diff) = first_difference_function(project_index, arg_types.clone(), &patterns) {
        // println!("Diff: {:#?}", diff);
        // There was a difference that lets us distinguish some of the patterns into different branches.
        let diff_reason = diff.reason;
        let diff_place = diff.place;
        match diff_reason {
            PatternMismatchReason::EnumDiscriminant {
                enum_name,
                enum_parameters,
                cases,
            } => {
                // Create a match operation for each enum discriminant case.
                // If a pattern for a given case does not reference the enum's discriminant, we'll
                // replace it with a dummy pattern that references the discriminant we just matched.
                let cases_matched = cases
                    .into_iter()
                    .map(|(name, cases)| {
                        let new_cases = cases
                            .into_iter()
                            .map(|id| {
                                let enum_fields = if let TypeDeclarationTypeI::Enum(enumi) =
                                    &project_index[&enum_name.source_file].types[&enum_name.name]
                                        .decl_type
                                {
                                    enumi
                                        .variants
                                        .iter()
                                        .find_map(|variant| {
                                            if variant.name.name == name {
                                                Some(
                                                    variant
                                                        .type_ctor
                                                        .fields
                                                        .iter()
                                                        .map(|(name, ty)| {
                                                            (name.name.clone(), ty.clone())
                                                        })
                                                        .collect::<Vec<_>>(),
                                                )
                                            } else {
                                                None
                                            }
                                        })
                                        .unwrap()
                                } else {
                                    unreachable!()
                                };

                                let replacement = Pattern::TypeConstructor {
                                    type_ctor: TypeConstructorInvocation {
                                        data_type: enum_name.clone(),
                                        variant: Some(name.clone()),
                                        // I *think* that num_parameters is not relevant here.
                                        num_parameters: 0,
                                        range,
                                    },
                                    fields: enum_fields
                                        .into_iter()
                                        .map(|(name, ty)| {
                                            let pattern = Pattern::Unknown(range);
                                            (NameP { name, range }, ty, pattern)
                                        })
                                        .collect(),
                                };

                                (
                                    reference_place_function(
                                        diff_place.clone(),
                                        replacement,
                                        patterns[id].clone(),
                                    ),
                                    blocks[id],
                                )
                            })
                            .collect();
                        (
                            name,
                            perform_match_function(
                                project_index,
                                ctx,
                                range,
                                arg_types.clone(),
                                new_cases,
                            ),
                        )
                    })
                    .collect::<HashMap<_, _>>();

                // Now, each case has been successfully pattern matched to its entirety.
                // Finally, construct the switch statement to switch between the given cases.
                ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator {
                        range,
                        kind: TerminatorKind::SwitchDiscriminant {
                            enum_name,
                            enum_parameters,
                            enum_place: diff_place,
                            cases: cases_matched,
                        },
                    },
                })
            }
            PatternMismatchReason::Constant { cases, default } => {
                // Create a match operation for each value.
                // If a pattern for a given case does not reference the value, we'll
                // replace it with a dummy pattern that requires the value we just matched.
                let cases_matched = cases
                    .into_iter()
                    .map(|(value, cases)| {
                        let new_cases = cases
                            .into_iter()
                            .map(|id| {
                                let replacement = Pattern::Constant { range, value };

                                (
                                    reference_place_function(
                                        diff_place.clone(),
                                        replacement,
                                        patterns[id].clone(),
                                    ),
                                    blocks[id],
                                )
                            })
                            .collect();
                        (
                            value,
                            perform_match_function(
                                project_index,
                                ctx,
                                range,
                                arg_types.clone(),
                                new_cases,
                            ),
                        )
                    })
                    .collect::<HashMap<_, _>>();

                let default = {
                    if default.is_empty() {
                        // LLVM requires an else block.
                        *cases_matched.values().next().unwrap()
                    } else {
                        let new_cases = default
                            .into_iter()
                            .map(|id| (patterns[id].clone(), blocks[id]))
                            .collect();
                        perform_match_function(project_index, ctx, range, arg_types, new_cases)
                    }
                };

                // Now, each case has been successfully pattern matched to its entirety.
                // Finally, construct the switch statement to switch between the given cases.
                ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator {
                        range,
                        kind: TerminatorKind::SwitchConstant {
                            place: diff_place,
                            cases: cases_matched,
                            default,
                        },
                    },
                })
            }
        }
    } else {
        // There was no difference between the patterns.
        // The first case listed is the "correct" one, since we match earlier cases first.
        blocks[0]
    }
}

pub(crate) struct BoundPatternVariables {
    /// A list of statements that will initialise the pattern variables.
    pub statements: Vec<Statement>,
    /// The list of actual variables that we bind.
    pub bound_variables: Vec<LocalVariableName>,
}

/// Creates a local variable for each bound variable in a pattern, assuming that the given value
/// has the given pattern, and the given type.
/// Returns statements that will initialise these variables, or statements that will *drop* the value
/// if no variable initialisation is required.
pub(crate) fn bind_pattern_variables(
    ctx: &mut DefinitionTranslationContext,
    index: &ProjectIndex,
    value: Place,
    pat: &Pattern,
    ty: Type,
) -> BoundPatternVariables {
    match pat {
        Pattern::Named(name) => {
            let var = ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty,
                name: Some(name.name.clone()),
            });

            // Initialise this local variable with the supplied value.
            let assign = Statement {
                range: name.range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(var),
                    source: Rvalue::Move(value),
                },
            };

            BoundPatternVariables {
                statements: vec![assign],
                bound_variables: vec![LocalVariableName::Local(var)],
            }
        }
        Pattern::Constant { .. } => BoundPatternVariables {
            statements: Vec::new(),
            bound_variables: Vec::new(),
        },
        Pattern::TypeConstructor { type_ctor, fields } => {
            // Bind each field individually, then chain all the blocks together.
            // First work out the type parameters used for this type.
            let decl = &index[&type_ctor.data_type.source_file].types[&type_ctor.data_type.name];
            let named_type_parameters = match &decl.decl_type {
                TypeDeclarationTypeI::Data(datai) => &datai.type_params,
                TypeDeclarationTypeI::Enum(enumi) => &enumi.type_params,
            };
            let concrete_type_parameters = if let Type::Named { ref parameters, .. } = ty {
                parameters
            } else {
                unreachable!()
            };

            let results = fields
                .iter()
                .map(|(field_name, ty, pat)| {
                    bind_pattern_variables(
                        ctx,
                        index,
                        value
                            .clone()
                            .then(if let Some(variant) = type_ctor.variant.clone() {
                                PlaceSegment::EnumField {
                                    variant,
                                    field: field_name.name.clone(),
                                }
                            } else {
                                PlaceSegment::DataField {
                                    field: field_name.name.clone(),
                                }
                            }),
                        pat,
                        replace_type_variables(
                            ty.clone(),
                            named_type_parameters,
                            concrete_type_parameters,
                        ),
                    )
                })
                .map(|result| (result.statements, result.bound_variables))
                .collect::<Vec<_>>();

            let mut statements = Vec::new();
            let mut bound_variables = Vec::new();
            for (more_statements, more_bound_variables) in results {
                statements.extend(more_statements);
                bound_variables.extend(more_bound_variables);
            }

            BoundPatternVariables {
                statements,
                bound_variables,
            }
        }
        Pattern::Impl { fields, .. } => {
            let (aspect_name, concrete_type_parameters) =
                if let Type::Impl { name, parameters } = &ty {
                    (name, parameters)
                } else {
                    unreachable!()
                };

            // Bind each field individually, then chain all the blocks together.
            // First work out the type parameters used for this type.
            let decl = &index[&aspect_name.source_file].aspects[&aspect_name.name];
            let named_type_parameters = &decl.type_variables;

            let results = fields
                .iter()
                .map(|(field_name, ty, pat)| {
                    bind_pattern_variables(
                        ctx,
                        index,
                        value.clone().then(PlaceSegment::ImplField {
                            field: field_name.name.clone(),
                        }),
                        pat,
                        replace_type_variables(
                            ty.clone(),
                            named_type_parameters,
                            concrete_type_parameters,
                        ),
                    )
                })
                .map(|result| (result.statements, result.bound_variables))
                .collect::<Vec<_>>();

            let mut statements = Vec::new();
            let mut bound_variables = Vec::new();
            for (more_statements, more_bound_variables) in results {
                statements.extend(more_statements);
                bound_variables.extend(more_bound_variables);
            }

            BoundPatternVariables {
                statements,
                bound_variables,
            }
        }
        Pattern::Function { .. } => {
            unreachable!("functions are forbidden in arg patterns")
        }
        Pattern::Unknown(range) => {
            // Drop this variable.
            let range = *range;
            let local = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });
            let move_stmt = Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(local),
                    source: Rvalue::Move(value),
                },
            };
            let drop_stmt = Statement {
                range,
                kind: StatementKind::DropIfAlive {
                    variable: LocalVariableName::Local(local),
                },
            };
            BoundPatternVariables {
                statements: vec![move_stmt, drop_stmt],
                bound_variables: Vec::new(),
            }
        }
    }
}
