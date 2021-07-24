use std::collections::{BTreeMap, BTreeSet};

use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, SourceFileIdentifier},
};
use quill_mir::mir::{
    ArgumentIndex, BasicBlockId, ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableName,
    Place, Rvalue, Statement, StatementKind, TerminatorKind,
};

#[derive(Debug, Clone)]
enum OwnershipStatus {
    NotInitialised {
        /// Where was this variable defined, even though it was not initialised?
        definition: Range,
        block: BasicBlockId,
    },
    Owned {
        /// Where did we first gain ownership of this variable?
        assignment: Range,
        block: BasicBlockId,
    },
    Moved {
        /// Where did we move this variable?
        moved: Range,
        block: BasicBlockId,
    },
    Destructured {
        /// Where did we destructure this variable?
        destructured: Range,
        block: BasicBlockId,
    },
    /// Sometimes, this object is moved/owned, and sometimes not, depending on which basic blocks we pass through
    /// in the real control flow of the function.
    Conditional {
        /// The place that the conditional statuses were reconciled in.
        reconciled: Range,
        /// The block that the conditional statuses were reconciled in.
        block: BasicBlockId,
        /// Originally, this object is considered 'owned'. But if we pass through the given basic blocks, its ownership
        /// status is considered 'moved' into the given range.
        moved_into_blocks: BTreeMap<BasicBlockId, Range>,
        /// If we pass through the given blocks, its ownership status is considered 'destructured'.
        /// We must free its memory, but not call its drop code.
        destructured_in_blocks: BTreeMap<BasicBlockId, Range>,
        /// Through these paths, the object is still owned. Drop and free must be called.
        not_moved_blocks: BTreeMap<BasicBlockId, Range>,
    },
}

#[derive(Debug, Clone)]
struct OwnershipStatuses {
    locals: BTreeMap<LocalVariableName, OwnershipStatus>,
}

/// The input MIR is not expected to handle dropping/freeing at all, and this function
/// works out when we need to drop and free local variables.
///
/// In particular, this function checks whether data is owned when it is used or referenced.
/// We walk through all branches of the control flow graph deducing ownership (but not borrow) status.
pub(crate) fn check_ownership(
    source_file: &SourceFileIdentifier,
    def: &mut DefinitionM,
    messages: &mut Vec<ErrorMessage>,
) {
    // eprintln!("{}", def);
    let range = def.range;

    if let DefinitionBodyM::PatternMatch(cfg) = &mut def.body {
        let statuses = OwnershipStatuses {
            locals: def
                .local_variable_names
                .iter()
                .map(|(name, info)| {
                    (
                        *name,
                        OwnershipStatus::NotInitialised {
                            definition: info.range,
                            block: BasicBlockId(0),
                        },
                    )
                })
                .chain((0..def.arity).into_iter().map(|i| {
                    (
                        LocalVariableName::Argument(ArgumentIndex(i as u64)),
                        OwnershipStatus::Owned {
                            assignment: range,
                            block: BasicBlockId(0),
                        },
                    )
                }))
                .collect(),
        };

        check_ownership_walk(source_file, cfg, messages, statuses);
    }
}

/// Traverse every route between blocks, working out the usages of each variable in each block.
/// The input CFG must not have any cycles, and must be topologically sorted.
fn check_ownership_walk(
    source_file: &SourceFileIdentifier,
    cfg: &mut ControlFlowGraph,
    messages: &mut Vec<ErrorMessage>,
    original_statuses: OwnershipStatuses,
) {
    let mut original_statuses = Some(original_statuses);

    // First, find a list of the transitions of the control flow graph in reverse.
    // We need to track how each block is arrived at.
    let mut predecessors = cfg
        .basic_blocks
        .keys()
        .map(|block| (*block, BTreeSet::new()))
        .collect::<BTreeMap<BasicBlockId, BTreeSet<BasicBlockId>>>();

    for (block_id, block) in &cfg.basic_blocks {
        match &block.terminator.kind {
            TerminatorKind::Goto(target) => {
                predecessors.get_mut(target).unwrap().insert(*block_id);
            }
            TerminatorKind::SwitchDiscriminant { cases, .. } => {
                for target in cases.values() {
                    predecessors.get_mut(target).unwrap().insert(*block_id);
                }
            }
            TerminatorKind::SwitchConstant { cases, .. } => {
                for target in cases.values() {
                    predecessors.get_mut(target).unwrap().insert(*block_id);
                }
            }
            TerminatorKind::Invalid => unreachable!(),
            TerminatorKind::Return { .. } => {}
        }
    }

    // At the *end* of a given basic block, what are the ownership statuses of variables?
    let mut statuses = BTreeMap::<BasicBlockId, OwnershipStatuses>::new();

    // A list of blocks that we need to add drop instructions to, so that certain variables are actually dropped.
    let mut pending_drops = BTreeMap::<BasicBlockId, Vec<LocalVariableName>>::new();
    let mut pending_frees = BTreeMap::<BasicBlockId, Vec<LocalVariableName>>::new();

    // We know that the input graph is topologically sorted.
    // Therefore, we can iterate through each basic block in order, knowing that all of its
    // predecessors have already been computed.
    for (block_id, block) in &mut cfg.basic_blocks {
        // Work out the ownership statuses at the start of this block.
        let branch_statuses = predecessors[block_id]
            .iter()
            .map(|previous_block| (*previous_block, statuses[previous_block].clone()))
            .collect::<Vec<_>>();

        // Collate the statuses together.
        let mut block_statuses = if branch_statuses.is_empty() {
            assert!(*block_id == cfg.entry_point);
            original_statuses.take().unwrap()
        } else {
            collate_statuses(
                block.terminator.range,
                *block_id,
                branch_statuses,
                &mut pending_drops,
                &mut pending_frees,
            )
        };

        // For each statement in the block, compute how it changes ownership.
        for stmt in &block.statements {
            match &stmt.kind {
                StatementKind::Assign { target, source } => {
                    make_rvalue_used(
                        source_file,
                        messages,
                        &mut block_statuses,
                        stmt.range,
                        *block_id,
                        source.clone(),
                    );
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
                }
                StatementKind::AssignPhi { target, phi_cases } => {
                    for (_, case) in phi_cases {
                        // We don't need to worry about move checking much, since the only way a user can ever
                        // generate a phi node is by using a match expression, which automatically moves
                        // the result of each branch into the phi node without borrowing or anything.
                        // So, for the sake of borrowck, just pretend that the variable's been moved out.
                        *block_statuses.locals.get_mut(case).unwrap() = OwnershipStatus::Moved {
                            moved: stmt.range,
                            block: *block_id,
                        };
                    }
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
                }
                StatementKind::InstanceSymbol { target, .. } => {
                    // The target is now owned.
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
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
                        &mut block_statuses,
                        stmt.range,
                        *block_id,
                        *argument.clone(),
                    );
                    make_rvalue_used(
                        source_file,
                        messages,
                        &mut block_statuses,
                        stmt.range,
                        *block_id,
                        *function.clone(),
                    );
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
                }
                StatementKind::ConstructData { fields, target, .. } => {
                    for field_value in fields.values() {
                        make_rvalue_used(
                            source_file,
                            messages,
                            &mut block_statuses,
                            stmt.range,
                            *block_id,
                            field_value.clone(),
                        );
                    }
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
                }
                StatementKind::ConstructImpl {
                    target,
                    definitions,
                    ..
                } => {
                    // TODO: For now, we can't pass local variables into impls.
                    // When this is implemented, we can add more things here.

                    // Move the definitions out.
                    for def in definitions.values() {
                        make_rvalue_used(
                            source_file,
                            messages,
                            &mut block_statuses,
                            stmt.range,
                            *block_id,
                            Rvalue::Move(Place::new(*def)),
                        );
                    }

                    // The target is now owned.
                    make_owned(&mut block_statuses, stmt.range, *target, *block_id);
                }
                _ => unreachable!(),
            }
        }

        // If this is a block that returns from the function,
        // add drop instructions for all unused variables.
        if let TerminatorKind::Return { value } = &block.terminator.kind {
            for (variable, status) in &block_statuses.locals {
                if variable == value {
                    continue;
                }
                match status {
                    OwnershipStatus::NotInitialised { .. } => {}
                    OwnershipStatus::Owned { .. } => {
                        block.statements.push(Statement {
                            range: block.terminator.range,
                            kind: StatementKind::Drop {
                                variable: *variable,
                            },
                        });
                        block.statements.push(Statement {
                            range: block.terminator.range,
                            kind: StatementKind::Free {
                                variable: *variable,
                            },
                        });
                    }
                    OwnershipStatus::Moved { .. } => {}
                    OwnershipStatus::Destructured { .. } => {
                        block.statements.push(Statement {
                            range: block.terminator.range,
                            kind: StatementKind::Free {
                                variable: *variable,
                            },
                        });
                    }
                    OwnershipStatus::Conditional { .. } => {}
                }
            }
        }

        // Store the new list of statuses into the statuses map.
        statuses.insert(*block_id, block_statuses);
    }

    // Create all of the drop/free instructions that were pending, created in the collate_statuses function.
    for (block_id, vars) in pending_drops {
        let block = cfg.basic_blocks.get_mut(&block_id).unwrap();
        for variable in vars {
            block.statements.push(Statement {
                range: block.terminator.range,
                kind: StatementKind::Drop { variable },
            });
            block.statements.push(Statement {
                range: block.terminator.range,
                kind: StatementKind::Free { variable },
            });
        }
    }
    for (block_id, vars) in pending_frees {
        let block = cfg.basic_blocks.get_mut(&block_id).unwrap();
        for variable in vars {
            block.statements.push(Statement {
                range: block.terminator.range,
                kind: StatementKind::Free { variable },
            });
        }
    }
}

/// Sometimes, control flow might branch into multiple directions. In this case, the ownership statuses
/// after each block may differ. This function unifies the possible ambiguity into a collective ownership
/// state that is true after the branch finishes.
fn collate_statuses(
    range: Range,
    block_id: BasicBlockId,
    branch_statuses: Vec<(BasicBlockId, OwnershipStatuses)>,
    pending_drops: &mut BTreeMap<BasicBlockId, Vec<LocalVariableName>>,
    pending_frees: &mut BTreeMap<BasicBlockId, Vec<LocalVariableName>>,
) -> OwnershipStatuses {
    // Flatten the list of statuses into a map from local variable names to their potential statuses.
    let flattened =
        branch_statuses
            .into_iter()
            .fold(BTreeMap::new(), |mut acc, (block, statuses)| {
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
                (
                    variable,
                    collate_statuses_single(
                        variable,
                        range,
                        block_id,
                        branch_statuses,
                        pending_drops,
                        pending_frees,
                    ),
                )
            })
            .collect(),
    }
}

/// The branch statuses are disjoint events that could occur.
fn collate_statuses_single(
    variable: LocalVariableName,
    range: Range,
    block_id: BasicBlockId,
    branch_statuses: Vec<(BasicBlockId, OwnershipStatus)>,
    pending_drops: &mut BTreeMap<BasicBlockId, Vec<LocalVariableName>>,
    pending_frees: &mut BTreeMap<BasicBlockId, Vec<LocalVariableName>>,
) -> OwnershipStatus {
    // If one branch considers a variable not initialised, then the variable is
    // hidden from the outside scope. In this case, this variable contains the location
    // where the variable was defined.
    let mut not_initialised_but_defined_at = None;

    let mut moved_into_blocks = BTreeMap::new();
    let mut destructured_in_blocks = BTreeMap::new();
    let mut not_moved_blocks = BTreeMap::new();

    for (_block, status) in branch_statuses {
        match status {
            OwnershipStatus::NotInitialised { definition, .. } => {
                not_initialised_but_defined_at = Some(definition);
            }
            OwnershipStatus::Owned { assignment, block } => {
                not_moved_blocks.insert(block, assignment);
            }
            OwnershipStatus::Moved { moved, block } => {
                moved_into_blocks.insert(block, moved);
            }
            OwnershipStatus::Destructured {
                destructured,
                block,
            } => {
                destructured_in_blocks.insert(block, destructured);
            }
            OwnershipStatus::Conditional {
                reconciled, block, ..
            } => {
                moved_into_blocks.insert(block, reconciled);
            }
        }
    }

    if let Some(definition) = not_initialised_but_defined_at {
        OwnershipStatus::NotInitialised {
            definition,
            block: block_id,
        }
    } else if moved_into_blocks.is_empty() && destructured_in_blocks.is_empty() {
        OwnershipStatus::Owned {
            assignment: *not_moved_blocks.iter().next().unwrap().1,
            block: block_id,
        }
    } else if not_moved_blocks.is_empty() && destructured_in_blocks.is_empty() {
        OwnershipStatus::Moved {
            moved: *moved_into_blocks.iter().next().unwrap().1,
            block: block_id,
        }
    } else if moved_into_blocks.is_empty() && not_moved_blocks.is_empty() {
        OwnershipStatus::Destructured {
            destructured: *destructured_in_blocks.iter().next().unwrap().1,
            block: block_id,
        }
    } else {
        // If we have conditional ownership, then treat the variable as dropped, and
        // add drop/free instructions to the blocks in which the variable was not dropped/freed.
        for block in not_moved_blocks.keys() {
            pending_drops.entry(*block).or_default().push(variable);
        }
        for block in destructured_in_blocks.keys() {
            pending_frees.entry(*block).or_default().push(variable);
        }
        OwnershipStatus::Conditional {
            reconciled: range,
            block: block_id,
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
    block_id: BasicBlockId,
    rvalue: Rvalue,
) {
    match rvalue {
        Rvalue::Move(place) => {
            // If we're moving out of a place contained inside a local variable, that variable is said to have been 'destructured'.
            make_used(
                source_file,
                messages,
                statuses,
                range,
                block_id,
                place.local,
                if place.projection.is_empty() {
                    UseType::Move
                } else {
                    UseType::Destructure
                },
            )
        }
        Rvalue::Borrow(local) => make_used(
            source_file,
            messages,
            statuses,
            range,
            block_id,
            local,
            UseType::Reference,
        ),
        Rvalue::Copy(local) => make_used(
            source_file,
            messages,
            statuses,
            range,
            block_id,
            local,
            UseType::Reference,
        ),
        Rvalue::Constant(_) => {}
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
    block_id: BasicBlockId,
    variable: LocalVariableName,
    use_type: UseType,
) {
    // Make sure that this variable is currently owned.
    // We shouldn't be able to use an uninitialised or dropped variable because of earlier scope checks.
    match statuses.locals.get(&variable).unwrap() {
        OwnershipStatus::NotInitialised { .. } => panic!("variable {} uninitialised", variable),
        OwnershipStatus::Owned { .. } => {}
        OwnershipStatus::Moved { moved, .. } => messages.push(ErrorMessage::new_with(
            format!(
                "this variable ({}) has already been moved out, so it cannot be used here",
                variable
            ),
            Severity::Error,
            Diagnostic::at(source_file, &range),
            HelpMessage {
                message: "previously moved here".to_string(),
                help_type: HelpType::Note,
                diagnostic: Diagnostic::at(source_file, moved),
            },
        )),
        OwnershipStatus::Destructured { destructured, .. } => {
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
            *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Moved {
                moved: range,
                block: block_id,
            }
        }
        UseType::Destructure => {
            *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Destructured {
                destructured: range,
                block: block_id,
            }
        }
        UseType::Reference => {}
    }
}

/// Adjusts the statuses to reflect that this value is now owned.
fn make_owned(
    statuses: &mut OwnershipStatuses,
    range: Range,
    variable: LocalVariableName,
    block_id: BasicBlockId,
) {
    // If this variable is currently alive, we need to translate this instruction into an unconditional drop instruction.
    // Otherwise, we need to add drop flags and drop the variable if and only if it's not been moved out so far.
    // Because the MIR is in SSA form, the variable cannot be owned already.
    *statuses.locals.get_mut(&variable).unwrap() = OwnershipStatus::Owned {
        assignment: range,
        block: block_id,
    };
}
