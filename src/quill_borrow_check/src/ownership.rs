use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
};
use quill_mir::mir::{
    ArgumentIndex, BasicBlockId, ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableName,
    Operand, Rvalue, Statement, StatementKind, TerminatorKind,
};

#[derive(Debug, Clone)]
enum OwnershipStatus {
    NotInitialised {
        /// Where was this variable defined, even though it was not initialised?
        definition: Range,
    },
    Owned {
        /// Where did we first gain ownership of this variable?
        assignment: Range,
    },
    Moved {
        /// Where did we move this variable?
        moved: Range,
    },
    Dropped {
        /// Where did we drop this variable?
        dropped: Range,
    },
    Destructured {
        /// Where did we destructure this variable?
        destructured: Range,
    },
    /// Sometimes, this object is moved/owned/dropped, and sometimes not, depending on which basic blocks we pass through
    /// in the real control flow of the function.
    Conditional {
        /// Originally, this object is considered 'owned'. But if we pass through the given basic blocks, its ownership
        /// status is considered 'moved' into the given range.
        moved_into_blocks: HashMap<BasicBlockId, Range>,
        /// If we pass through the given blocks, its ownership status is considered 'destructured'.
        /// We must free its memory, but not call its drop code.
        destructured_in_blocks: HashMap<BasicBlockId, Range>,
        /// Through these paths, the object is still owned. Drop and free must be called.
        not_moved_blocks: HashMap<BasicBlockId, Range>,
    },
}

#[derive(Clone)]
struct OwnershipStatuses {
    locals: HashMap<LocalVariableName, OwnershipStatus>,
}

/// Checks whether data is owned when it is used or referenced.
/// We walk through all branches of the control flow graph deducing ownership (but not borrow) status.
/// This allows us to insert StorageLive, StorageDead, and Drop instructions into the MIR.
/// In particular, we remove DropIfAlive instructions in this step, replacing them with hard drops, introducing drop flags if necessary.
pub(crate) fn check_ownership(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
) {
    // println!("{}", def);
    let range = def.range;

    let mut statuses = OwnershipStatuses {
        locals: def
            .local_variable_names
            .iter()
            .map(|(name, info)| {
                (
                    *name,
                    OwnershipStatus::NotInitialised {
                        definition: info.range,
                    },
                )
            })
            .chain((0..def.arity).into_iter().map(|i| {
                (
                    LocalVariableName::Argument(ArgumentIndex(i as u64)),
                    OwnershipStatus::Owned { assignment: range },
                )
            }))
            .collect(),
    };

    if let DefinitionBodyM::PatternMatch(cfg) = &mut def.body {
        check_ownership_walk(source_file, cfg, messages, &mut statuses, cfg.entry_point);

        // Now, check to make sure all variables are successfully moved out or dropped.
        // Otherwise, there is something dangling.
        for (name, stat) in statuses.locals {
            match stat {
                OwnershipStatus::Owned { assignment } => messages.push(ErrorMessage::new(
                    format!(
                        "local variable `{}` was not moved or dropped (this is a compiler bug)",
                        name
                    ),
                    Severity::Error,
                    Diagnostic::at(source_file, &assignment),
                )),
                OwnershipStatus::Moved { .. } => {}
                OwnershipStatus::Dropped { .. } => {}
                OwnershipStatus::Destructured { destructured } => messages.push(ErrorMessage::new(
                    format!(
                    "local variable `{}` was destructured but not freed (this is a compiler bug)",
                    name
                ),
                    Severity::Error,
                    Diagnostic::at(source_file, &destructured),
                )),
                OwnershipStatus::Conditional {
                    moved_into_blocks,
                    destructured_in_blocks,
                    not_moved_blocks,
                } => {
                    if !not_moved_blocks.is_empty() {
                        messages.push(ErrorMessage::new(
                        format!(
                            "local variable `{}` was not moved or dropped (this is a compiler bug): {:#?}; {:#?}; {:#?}",
                            name, moved_into_blocks, destructured_in_blocks, not_moved_blocks,
                        ),
                        Severity::Error,
                        Diagnostic::at(source_file, &range),
                    ));
                    }
                }
                OwnershipStatus::NotInitialised { .. } => {
                    // The local variable is hidden from this scope, so it must have already been dropped or moved.
                }
            }
        }
    }
}

/// Check the ownership at this point, adding this block id to the list of completed blocks.
/// This function may be called multiple times. The language guarantees that statuses will be updated the same way regardless
/// of when we call this function.
#[allow(clippy::needless_collect)]
fn check_ownership_walk(
    source_file: &SourceFileIdentifier,
    cfg: &mut ControlFlowGraph,
    messages: &mut Vec<ErrorMessage>,
    statuses: &mut OwnershipStatuses,
    block_id: BasicBlockId,
) {
    let block = cfg.basic_blocks.get_mut(&block_id).unwrap();

    // Iterate over each statement to check if that statement's action is ok to perform, given the current ownership of variables at this point.
    // If the statement is a drop (for example), we might need to add or remove statements, so it's not just a normal "for" loop.
    let mut i = 0;
    while i < block.statements.len() {
        // NOTE! The i++ statement happens HERE not at the end of the loop - this is done to prevent overflow!
        let stmt = &mut block.statements[i];
        i += 1;

        match &mut stmt.kind {
            StatementKind::Assign { target, source } => {
                make_rvalue_used(source_file, messages, statuses, stmt.range, source.clone());
                make_owned(statuses, stmt.range, *target);
            }
            StatementKind::InstanceSymbol { target, .. } => {
                // The target is now owned.
                make_owned(statuses, stmt.range, *target);
            }
            StatementKind::Apply {
                argument,
                function,
                target,
                ..
            } => {
                make_rvalue_used(
                    source_file,
                    messages,
                    statuses,
                    stmt.range,
                    *argument.clone(),
                );
                make_rvalue_used(
                    source_file,
                    messages,
                    statuses,
                    stmt.range,
                    *function.clone(),
                );
                make_owned(statuses, stmt.range, *target);
            }
            StatementKind::DropIfAlive { variable } => {
                let drop_stmts = make_dropped(statuses, stmt.range, *variable);
                let len = drop_stmts.len();
                block.statements.splice((i - 1)..i, drop_stmts);
                i += len;
                i -= 1;
            }
            StatementKind::Drop { variable } => {
                // In a previous run of this function, we dropped this variable.
                // So we call make_dropped like before, but don't update any instructions.
                make_dropped(statuses, stmt.range, *variable);
            }
            StatementKind::Free { .. } => {
                // In a previous run of this function, we freed this variable.
                // Don't update any instructions.
            }
            StatementKind::ConstructData { fields, target, .. } => {
                for field_value in fields.values() {
                    make_rvalue_used(
                        source_file,
                        messages,
                        statuses,
                        stmt.range,
                        field_value.clone(),
                    );
                }
                make_owned(statuses, stmt.range, *target);
            }
            _ => unreachable!(),
        }
    }

    // Now consider the block's terminator.
    // We can't express loops literally in Quill, so there's no worry about infinite recursion.
    let terminator_range = block.terminator.range;
    match &mut block.terminator.kind {
        TerminatorKind::Goto(target) => {
            let target = *target;
            check_ownership_walk(source_file, cfg, messages, statuses, target)
        }
        TerminatorKind::SwitchDiscriminant {
            enum_place, cases, ..
        } => {
            // Ensure that the enum place is OK to use.
            make_used(
                source_file,
                messages,
                statuses,
                terminator_range,
                enum_place.local,
                UseType::Reference,
            );

            // Now, walk on each branch and collate the results.
            // Clippy thinks I can elide the collect, but there's a lifetime issue if I do.
            let branches = cases.values().copied().collect::<Vec<_>>();
            let branch_statuses = branches
                .into_iter()
                .map(|target_block| {
                    let mut inner_statuses = statuses.clone();
                    check_ownership_walk(
                        source_file,
                        cfg,
                        messages,
                        &mut inner_statuses,
                        target_block,
                    );
                    (target_block, inner_statuses)
                })
                .collect::<Vec<_>>();
            *statuses = collate_statuses(terminator_range, branch_statuses);
        }
        TerminatorKind::SwitchConstant {
            place,
            cases,
            default,
        } => {
            // Ensure that the enum place is OK to use.
            make_used(
                source_file,
                messages,
                statuses,
                terminator_range,
                place.local,
                UseType::Reference,
            );

            // Now, walk on each branch and collate the results.
            // Clippy thinks I can elide the collect, but there's a lifetime issue if I do.
            let branches = cases
                .values()
                .copied()
                .chain(std::iter::once(*default))
                .collect::<Vec<_>>();
            let branch_statuses = branches
                .into_iter()
                .map(|target_block| {
                    let mut inner_statuses = statuses.clone();
                    check_ownership_walk(
                        source_file,
                        cfg,
                        messages,
                        &mut inner_statuses,
                        target_block,
                    );
                    (target_block, inner_statuses)
                })
                .collect::<Vec<_>>();
            *statuses = collate_statuses(terminator_range, branch_statuses);
        }
        TerminatorKind::Invalid => {}
        TerminatorKind::Return { value } => {
            make_used(
                source_file,
                messages,
                statuses,
                terminator_range,
                *value,
                UseType::Move,
            );
        }
    }
}

/// Sometimes, control flow might branch into multiple directions. In this case, the ownership statuses
/// after each block may differ. This function unifies the possible ambiguity into a collective ownership
/// state that is true after the branch finishes.
fn collate_statuses(
    range: Range,
    branch_statuses: Vec<(BasicBlockId, OwnershipStatuses)>,
) -> OwnershipStatuses {
    // Flatten the list of statuses into a map from local variable names to their potential statuses.
    let flattened =
        branch_statuses
            .into_iter()
            .fold(HashMap::new(), |mut acc, (block, statuses)| {
                for (k, v) in statuses.locals {
                    acc.entry(k).or_insert_with(Vec::new).push((block, v));
                }
                acc
            });

    // Then, for each local variable, collate the potential statuses.
    OwnershipStatuses {
        locals: flattened
            .into_iter()
            .map(|(variable, branch_statuses)| {
                (variable, collate_statuses_single(range, branch_statuses))
            })
            .collect(),
    }
}

/// The branch statuses are disjoint events that could occur.
fn collate_statuses_single(
    range: Range,
    branch_statuses: Vec<(BasicBlockId, OwnershipStatus)>,
) -> OwnershipStatus {
    // If one branch considers a variable not initialised, then the variable is
    // hidden from the outside scope. In this case, this variable contains the location
    // where the variable was defined.
    let mut not_initialised_but_defined_at = None;

    let mut moved_into_blocks = HashMap::new();
    let mut destructured_in_blocks = HashMap::new();
    let mut not_moved_blocks = HashMap::new();

    for (block, status) in branch_statuses {
        match status {
            OwnershipStatus::NotInitialised { definition } => {
                not_initialised_but_defined_at = Some(definition);
            }
            OwnershipStatus::Owned { assignment } => {
                not_moved_blocks.insert(block, assignment);
            }
            OwnershipStatus::Moved { moved } => {
                moved_into_blocks.insert(block, moved);
            }
            OwnershipStatus::Dropped { dropped } => {
                moved_into_blocks.insert(block, dropped);
            }
            OwnershipStatus::Destructured { destructured } => {
                destructured_in_blocks.insert(block, destructured);
            }
            OwnershipStatus::Conditional {
                moved_into_blocks: m,
                destructured_in_blocks: d,
                not_moved_blocks: n,
            } => {
                for (k, v) in m {
                    moved_into_blocks.insert(k, v);
                }
                for (k, v) in d {
                    destructured_in_blocks.insert(k, v);
                }
                for (k, v) in n {
                    not_moved_blocks.insert(k, v);
                }
            }
        }
    }

    if let Some(definition) = not_initialised_but_defined_at {
        OwnershipStatus::NotInitialised { definition }
    } else if moved_into_blocks.is_empty() && destructured_in_blocks.is_empty() {
        OwnershipStatus::Owned { assignment: range }
    } else if not_moved_blocks.is_empty() && destructured_in_blocks.is_empty() {
        OwnershipStatus::Moved { moved: range }
    } else if moved_into_blocks.is_empty() && not_moved_blocks.is_empty() {
        OwnershipStatus::Destructured {
            destructured: range,
        }
    } else {
        OwnershipStatus::Conditional {
            moved_into_blocks,
            destructured_in_blocks,
            not_moved_blocks,
        }
    }
}

/// Like `make_used` but takes an `Rvalue`.
fn make_rvalue_used(
    source_file: &SourceFileIdentifier,
    messages: &mut Vec<ErrorMessage>,
    statuses: &mut OwnershipStatuses,
    range: Range,
    rvalue: Rvalue,
) {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) => {
            // If we're moving out of a place contained inside a local variable, that variable is said to have been 'destructured'.
            make_used(
                source_file,
                messages,
                statuses,
                range,
                place.local,
                if place.projection.is_empty() {
                    UseType::Move
                } else {
                    UseType::Destructure
                },
            )
        }
        Rvalue::Use(Operand::Copy(place)) => make_used(
            source_file,
            messages,
            statuses,
            range,
            place.local,
            UseType::Reference,
        ),
        Rvalue::Use(Operand::Constant(_)) => {}
        Rvalue::Borrow(local) => make_used(
            source_file,
            messages,
            statuses,
            range,
            local,
            UseType::Reference,
        ),
    }
}

enum UseType {
    Move,
    Destructure,
    /// Just a copy or a borrow, doesn't affect dropping/freeing at all.
    Reference,
}

/// Adjusts the statuses to reflect that this value has now been used.
/// Emits an error message if this variable is not accessible from the current scope.
/// If `move_out` is true, update the status to now consider the variable "moved out".
/// TODO turn this into a proper usage checker
fn make_used(
    source_file: &SourceFileIdentifier,
    messages: &mut Vec<ErrorMessage>,
    statuses: &mut OwnershipStatuses,
    range: Range,
    variable: LocalVariableName,
    use_type: UseType,
) {
    // Make sure that this variable is currently owned.
    // We shouldn't be able to use an uninitialised or dropped variable because of earlier scope checks.
    match statuses.locals.get(&variable).unwrap() {
        OwnershipStatus::NotInitialised { .. } => unreachable!(),
        OwnershipStatus::Owned { .. } => {}
        OwnershipStatus::Moved { moved } => messages.push(ErrorMessage::new_with(
            "this variable has already been moved out, so it cannot be used here".to_string(),
            Severity::Error,
            Diagnostic::at(source_file, &range),
            HelpMessage {
                message: "previously moved here".to_string(),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, moved),
            },
        )),
        OwnershipStatus::Dropped { .. } => unreachable!(),
        OwnershipStatus::Destructured { destructured } => {
            // It's syntactically impossible to destructure a variable *and* keep its value,
            // since the only way to destructure something is to pattern match it.
            // So it's safe to destructure a variable multiple times - MIR uses this semantic
            // to express destructuring multiple fields of an object.
            if !matches!(use_type, UseType::Destructure) {
                messages.push(ErrorMessage::new_with(
                    "this variable has already been destructured, so it cannot be used here"
                        .to_string(),
                    Severity::Error,
                    Diagnostic::at(source_file, &range),
                    HelpMessage {
                        message: "previously destructured here".to_string(),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(source_file, destructured),
                    },
                ))
            }
        }
        OwnershipStatus::Conditional {
            moved_into_blocks,
            destructured_in_blocks,
            ..
        } => messages.push(ErrorMessage::new_with_many(
            "this variable might have already been moved out, so it cannot be used here"
                .to_string(),
            Severity::Error,
            Diagnostic::at(source_file, &range),
            moved_into_blocks
                .values()
                .map(|moved| HelpMessage {
                    message: "may have been previously moved here".to_string(),
                    help_type: HelpType::Note,
                    diagnostic: Diagnostic::at(source_file, moved),
                })
                .chain(
                    destructured_in_blocks
                        .values()
                        .map(|destructured| HelpMessage {
                            message: "may have been previously destructured here".to_string(),
                            help_type: HelpType::Note,
                            diagnostic: Diagnostic::at(source_file, destructured),
                        }),
                )
                .collect(),
        )),
    }

    match use_type {
        UseType::Move => {
            *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Moved { moved: range }
        }
        UseType::Destructure => {
            *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Destructured {
                destructured: range,
            }
        }
        UseType::Reference => {}
    }
}

/// Adjusts the statuses to reflect that this value is now owned.
fn make_owned(statuses: &mut OwnershipStatuses, range: Range, variable: LocalVariableName) {
    // If this variable is currently alive, we need to translate this instruction into an unconditional drop instruction.
    // Otherwise, we need to add drop flags and drop the variable if and only if it's not been moved out so far.
    // Because the MIR is in SSA form, the variable cannot be owned already.
    *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Owned { assignment: range };
}

/// Adjusts the statuses to reflect that this value is now dropped.
/// If this was an invalid operation to perform, the output messages will reflect this.
/// Returns the statement(s) that will perform the actual drop (if required).
fn make_dropped(
    statuses: &mut OwnershipStatuses,
    range: Range,
    variable: LocalVariableName,
) -> Vec<Statement> {
    // If this variable is currently alive, we need to translate this instruction into an unconditional drop instruction.
    // Otherwise, we need to add drop flags and drop the variable if and only if it's not been moved out so far.
    let stat = statuses.locals.get_mut(&variable).unwrap();
    match stat {
        OwnershipStatus::NotInitialised { .. } => unreachable!(),
        OwnershipStatus::Owned { .. } => {
            // Unconditionally drop this variable.
            *stat = OwnershipStatus::Dropped { dropped: range };
            vec![
                Statement {
                    range,
                    kind: StatementKind::Drop { variable },
                },
                Statement {
                    range,
                    kind: StatementKind::Free { variable },
                },
            ]
        }
        OwnershipStatus::Moved { .. } => {
            // Unconditionally do not drop this variable. It's already been moved out.
            Vec::new()
        }
        OwnershipStatus::Dropped { .. } => {
            // Unconditionally do not drop this variable. It's already been dropped.
            Vec::new()
        }
        OwnershipStatus::Destructured { .. } => {
            // Unconditionally do not drop this variable, but free its memory.
            vec![Statement {
                range,
                kind: StatementKind::Free { variable },
            }]
        }
        OwnershipStatus::Conditional { .. } => {
            // Maybe drop this variable, depending on drop flags.
            panic!("implement drop flags");
        }
    }
}
