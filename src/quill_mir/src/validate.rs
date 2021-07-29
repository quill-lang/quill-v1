use std::{
    collections::BTreeMap,
    fmt::{Debug, Display},
};

use quill_common::location::SourceFileIdentifier;
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    mir::{
        BasicBlock, BasicBlockId, DefinitionBodyM, DefinitionM, LocalVariableInfo,
        LocalVariableName, PlaceSegment, Rvalue, Statement, StatementKind, Terminator,
        TerminatorKind,
    },
    SourceFileMIR,
};

pub(crate) struct ValidationError<'a> {
    pub def_name: &'a str,
    pub block_id: BasicBlockId,
    /// If absent, the error was in the terminator.
    pub statement_id: Option<usize>,
    pub message: String,
}
pub(crate) type ValidationResult<'a> = Result<(), ValidationError<'a>>;

/// Ensure that the generated MIR is valid.
/// If it was invalid, this function will panic; an internal compiler error was detected.
///
/// Specifically, this checks every instruction and
/// terminator to ensure that the types match what would be expected.
/// It also verifies that the basic blocks are in a topologically sorted order.
pub(crate) fn validate<'a>(
    project_index: &ProjectIndex,
    source_file: &SourceFileIdentifier,
    mir: &'a SourceFileMIR,
) -> ValidationResult<'a> {
    for (def_name, def) in &mir.definitions {
        if let DefinitionBodyM::PatternMatch(body) = &def.body {
            for (block_id, block) in &body.basic_blocks {
                for (statement_id, statement) in block.statements.iter().enumerate() {
                    validate_stmt(
                        project_index,
                        &mir.definitions,
                        source_file,
                        &def.local_variable_names,
                        statement,
                    )
                    .map_err(|message| ValidationError {
                        def_name,
                        block_id: *block_id,
                        statement_id: Some(statement_id),
                        message,
                    })?;
                }
                validate_terminator(
                    project_index,
                    &def.local_variable_names,
                    &block.terminator,
                    *block_id,
                )
                .map_err(|message| ValidationError {
                    def_name,
                    block_id: *block_id,
                    statement_id: None,
                    message,
                })?;
            }
        }
    }
    Ok(())
}

/// Computes the expected type of this rvalue.
fn rvalue_type(
    project_index: &ProjectIndex,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Result<Type, String> {
    match rvalue {
        Rvalue::Move(place) => {
            let mut ty = locals[&place.local].ty.clone();
            for segment in &place.projection {
                match segment {
                    PlaceSegment::DataField { field } => {
                        if let Type::Named { name, parameters } = ty {
                            if let TypeDeclarationTypeI::Data(datai) =
                                &project_index[&name.source_file].types[&name.name].decl_type
                            {
                                if let Some(next_ty) =
                                    datai.type_ctor.fields.iter().find_map(|(name, ty)| {
                                        if name.name == *field {
                                            Some(replace_type_variables(
                                                ty.clone(),
                                                &datai.type_params,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                {
                                    ty = next_ty;
                                } else {
                                    return Err(format!(
                                        "tried to access non-existent field {} of type {}",
                                        field,
                                        Type::Named { name, parameters }
                                    ));
                                }
                            } else {
                                return Err(format!(
                                    "tried to access field {} of type {}",
                                    field,
                                    Type::Named { name, parameters }
                                ));
                            }
                        } else {
                            return Err(format!("tried to access field {} of type {}", field, ty));
                        }
                    }
                    PlaceSegment::EnumField { variant, field } => todo!(),
                    PlaceSegment::EnumDiscriminant => todo!(),
                    PlaceSegment::Constant => todo!(),
                    PlaceSegment::ImplField { field } => todo!(),
                }
            }
            Ok(ty)
        }
        Rvalue::Borrow(place) => todo!(),
        Rvalue::Copy(place) => todo!(),
        Rvalue::Constant(place) => todo!(),
    }
}

fn validate_stmt(
    project_index: &ProjectIndex,
    local_defs: &BTreeMap<String, DefinitionM>,
    source_file: &SourceFileIdentifier,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    statement: &Statement,
) -> Result<(), String> {
    fn assert_eq<T: Display + PartialEq>(l: T, r: T, reason: &str) -> Result<(), String> {
        if l == r {
            Ok(())
        } else {
            Err(format!("mismatch: {} != {} ({})", l, r, reason))
        }
    }

    match &statement.kind {
        StatementKind::Assign { target, source } => assert_eq(
            &locals[target].ty,
            &rvalue_type(project_index, locals, source)?,
            "assigning variable",
        ),
        StatementKind::AssignPhi { target, phi_cases } => todo!(),
        StatementKind::InstanceSymbol {
            name,
            type_variables,
            target,
        } => {
            // The symbol could be a lambda defined in this source file.
            // In this case, its type is not stored in the project index.
            let expected_type = if name.source_file == *source_file {
                let def = &local_defs[&name.name];
                replace_type_variables(def.symbol_type(), &def.type_variables, type_variables)
            } else {
                let def = &project_index[&name.source_file].definitions[&name.name];
                replace_type_variables(def.symbol_type.clone(), &def.type_variables, type_variables)
            };
            assert_eq(&locals[target].ty, &expected_type, "instancing symbol")
        }
        StatementKind::Apply {
            argument,
            function,
            target,
            return_type,
            argument_type,
        } => todo!(),
        StatementKind::InvokeFunction {
            name,
            type_variables,
            target,
            arguments,
        } => todo!(),
        StatementKind::ConstructFunctionObject {
            name,
            type_variables,
            target,
            curry_steps,
            curried_arguments,
        } => todo!(),
        StatementKind::InvokeFunctionObject {
            func_object,
            target,
            additional_arguments,
            return_type,
            additional_argument_types,
        } => todo!(),
        StatementKind::Drop { variable } => todo!(),
        StatementKind::Free { variable } => todo!(),
        StatementKind::ConstructData {
            ty,
            variant,
            fields,
            target,
        } => todo!(),
        StatementKind::ConstructImpl {
            aspect,
            type_variables,
            definitions,
            target,
        } => todo!(),
    }
}

fn validate_terminator(
    project_index: &ProjectIndex,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    terminator: &Terminator,
    block_id: BasicBlockId,
) -> Result<(), String> {
    match &terminator.kind {
        TerminatorKind::Goto(target) => {
            if *target <= block_id {
                Err(format!(
                    "blocks were not topologically sorted: {} -> {}",
                    block_id, target
                ))
            } else {
                Ok(())
            }
        }
        TerminatorKind::SwitchDiscriminant {
            enum_name,
            enum_parameters,
            enum_place,
            cases,
        } => todo!(),
        TerminatorKind::SwitchConstant {
            place,
            cases,
            default,
        } => todo!(),
        TerminatorKind::Invalid => todo!(),
        TerminatorKind::Return { value } => todo!(),
    }
}
