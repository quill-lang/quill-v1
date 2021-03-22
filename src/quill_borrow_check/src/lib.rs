use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
};
use quill_mir::{
    ArgumentIndex, BasicBlockId, DefinitionM, LocalVariableName, Operand, Rvalue, SourceFileMIR,
    StatementKind, TerminatorKind,
};

/// Checks to make sure that borrows of data do not outlive the data they borrow,
/// and to make sure that once data is not used when it is not owned.
/// This mostly implements the algorithm described [here](https://rust-lang.github.io/rfcs/2094-nll.html),
/// notably excluding mutable references, since Quill does not have a notion of mutable references.
pub fn borrow_check(
    source_file: &SourceFileIdentifier,
    mut mir: SourceFileMIR,
) -> DiagnosticResult<SourceFileMIR> {
    let mut messages = Vec::new();
    for (_def_name, def) in mir.definitions.iter_mut() {
        borrow_check_def(source_file, def, &mut messages);
    }
    DiagnosticResult::ok_with_many(mir, messages)
}

/// Walk through the control flow graph, generating and solving lifetime constraints.
fn borrow_check_def(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
) {
    // First, check to see if data ownership is valid.
    // Then, we'll check to see if lifetimes are valid.
    // Currently, lifetimes and borrowing are not features of the language, so we'll just do data ownership for now.

    check_ownership(source_file, def, messages);
}

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
    /// Sometimes, this object is moved/owned/dropped, and sometimes not, depending on which basic blocks we pass through
    /// in the real control flow of the function.
    Conditional {
        /// Originally, this object is considered 'owned'. But if we pass through the given basic blocks, its ownership
        /// status is considered 'moved' into the given range.
        moved_into_blocks: HashMap<BasicBlockId, Range>,
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
#[allow(clippy::clone_on_copy)]
fn check_ownership(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
) {
    let range = def.control_flow_graph.basic_blocks[&def.entry_point]
        .terminator
        .range;

    let mut statuses = OwnershipStatuses {
        locals: def
            .local_variable_names
            .iter()
            .map(|(name, info)| {
                (
                    // Clippy thinks I can remove `clone`, but then the borrow's lifetime has to include the `chain` call.
                    name.clone(),
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

    check_ownership_walk(source_file, def, messages, &mut statuses, def.entry_point);

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
            OwnershipStatus::Conditional {
                moved_into_blocks,
                not_moved_blocks,
            } => messages.push(ErrorMessage::new(
                format!(
                    "local variable `{}` was not moved or dropped (this is a compiler bug): {:#?}; {:#?}",
                    name, moved_into_blocks, not_moved_blocks,
                ),
                Severity::Error,
                Diagnostic::at(source_file, &range),
            )),
            OwnershipStatus::NotInitialised { .. } => unreachable!(),
        }
    }
}

/// Check the ownership at this point.
#[allow(clippy::needless_collect)]
fn check_ownership_walk(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
    statuses: &mut OwnershipStatuses,
    block_id: BasicBlockId,
) {
    let block = def
        .control_flow_graph
        .basic_blocks
        .get_mut(&block_id)
        .unwrap();

    // Iterate over each statement to check if that statement's action is ok to perform, given the current ownership of variables at this point.
    // If the statement is a drop (for example), we might need to add or remove statements, so it's not just a normal "for" loop.
    let mut i: isize = 0;
    while (i as usize) < block.statements.len() {
        let stmt = &mut block.statements[i as usize];
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
            } => {
                make_rvalue_used(
                    source_file,
                    messages,
                    statuses,
                    stmt.range,
                    argument.clone(),
                );
                make_rvalue_used(
                    source_file,
                    messages,
                    statuses,
                    stmt.range,
                    function.clone(),
                );
                make_owned(statuses, stmt.range, *target);
            }
            StatementKind::StorageLive(_) => unreachable!(),
            StatementKind::StorageDead(_) => unreachable!(),
            StatementKind::DropIfAlive { variable } => {
                let drop_stmt = make_dropped(statuses, stmt.range, *variable);
                if let Some(drop_stmt) = drop_stmt {
                    stmt.kind = drop_stmt;
                } else {
                    block.statements.remove(i as usize);
                    i -= 1;
                }
            }
            StatementKind::Drop { .. } => unreachable!(),
            StatementKind::CreateLambda { .. } => panic!("lambdas not implemented"),
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
        }
        i += 1;
    }

    // Now consider the block's terminator.
    // We can't express loops literally in Quill, so there's no worry about infinite recursion.
    let terminator_range = block.terminator.range;
    match &mut block.terminator.kind {
        TerminatorKind::Goto(target) => {
            let target = *target;
            check_ownership_walk(source_file, def, messages, statuses, target)
        }
        TerminatorKind::SwitchDiscriminator {
            enum_place, cases, ..
        } => {
            // Ensure that the enum place is OK to use.
            make_used(
                source_file,
                messages,
                statuses,
                terminator_range,
                enum_place.local,
                false,
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
                        def,
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
                true,
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
    let mut defined_at = None;
    let mut initialised = false;

    let mut moved_into_blocks = HashMap::new();
    let mut not_moved_blocks = HashMap::new();

    for (block, status) in branch_statuses {
        match status {
            OwnershipStatus::NotInitialised { definition } => {
                defined_at = Some(definition);
                not_moved_blocks.insert(block, definition);
            }
            OwnershipStatus::Owned { assignment } => {
                initialised = true;
                not_moved_blocks.insert(block, assignment);
            }
            OwnershipStatus::Moved { moved } => {
                moved_into_blocks.insert(block, moved);
            }
            OwnershipStatus::Dropped { dropped } => {
                moved_into_blocks.insert(block, dropped);
            }
            OwnershipStatus::Conditional {
                moved_into_blocks: m,
                not_moved_blocks: n,
            } => {
                for (k, v) in m {
                    moved_into_blocks.insert(k, v);
                }
                for (k, v) in n {
                    not_moved_blocks.insert(k, v);
                }
            }
        }
    }

    if moved_into_blocks.is_empty() {
        if initialised {
            OwnershipStatus::Owned { assignment: range }
        } else {
            OwnershipStatus::NotInitialised {
                definition: defined_at.unwrap(),
            }
        }
    } else if not_moved_blocks.is_empty() {
        OwnershipStatus::Moved { moved: range }
    } else {
        OwnershipStatus::Conditional {
            moved_into_blocks,
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
            make_used(source_file, messages, statuses, range, place.local, true)
        }
        Rvalue::Use(Operand::Copy(place)) => {
            make_used(source_file, messages, statuses, range, place.local, false)
        }
        Rvalue::Use(Operand::Constant(_)) => {}
    }
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
    move_out: bool,
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
        OwnershipStatus::Conditional {
            moved_into_blocks, ..
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
                .collect(),
        )),
    }

    if move_out {
        *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Moved { moved: range };
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
/// Returns the statement that will perform the actual drop (if required).
fn make_dropped(
    statuses: &mut OwnershipStatuses,
    range: Range,
    variable: LocalVariableName,
) -> Option<StatementKind> {
    // If this variable is currently alive, we need to translate this instruction into an unconditional drop instruction.
    // Otherwise, we need to add drop flags and drop the variable if and only if it's not been moved out so far.
    let stat = statuses.locals.get_mut(&variable).unwrap();
    match stat {
        OwnershipStatus::NotInitialised { .. } => unreachable!(),
        OwnershipStatus::Owned { .. } => {
            // Unconditionally drop this variable.
            *stat = OwnershipStatus::Dropped { dropped: range };
            Some(StatementKind::Drop { variable })
        }
        OwnershipStatus::Moved { .. } => {
            // Unconditionally do not drop this variable. It's already been moved out.
            None
        }
        OwnershipStatus::Dropped { .. } => {
            // Unconditionally do not drop this variable. It's already been dropped.
            None
        }
        OwnershipStatus::Conditional { .. } => {
            // Maybe drop this variable, depending on drop flags.
            panic!("implement drop flags");
        }
    }
}
