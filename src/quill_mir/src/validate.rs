use std::{collections::BTreeMap, fmt::Display, ops::Deref};

use quill_common::location::SourceFileIdentifier;
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_parser::expr_pat::ConstantValue;
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::{
    mir::{
        BasicBlockId, ControlFlowGraph, DefinitionBodyM, DefinitionM, LocalVariableInfo,
        LocalVariableName, Place, PlaceSegment, Rvalue, Statement, StatementKind, Terminator,
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
///
/// This does *not* verify that named symbols really exist in the project index; the validate function
/// will not produce nice error messages if a type or definition is not found.
/// This restriction is because MIR generation will never create new types out of nothing,
/// but the way those types are used might be unsound - and that's what we're checking in this function.
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
                        body,
                        *block_id,
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
                    &def.return_type,
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
        Rvalue::Move(place) => place_type(project_index, locals, place),
        Rvalue::Borrow(local) => Ok(Type::Borrow {
            ty: Box::new(locals[local].ty.clone()),
            borrow: None,
        }),
        Rvalue::Copy(local) => {
            if let Type::Borrow { ty, .. } = &locals[local].ty {
                Ok(ty.deref().clone())
            } else {
                Err(format!(
                    "type {} was not a borrow so cannot be copied",
                    &locals[local].ty
                ))
            }
        }
        Rvalue::Constant(value) => Ok(Type::Primitive(type_of_value(*value))),
    }
}

pub fn type_of_value(value: ConstantValue) -> PrimitiveType {
    match value {
        ConstantValue::Unit => PrimitiveType::Unit,
        ConstantValue::Bool(_) => PrimitiveType::Bool,
        ConstantValue::Int(_) => PrimitiveType::Int,
    }
}

fn place_type(
    project_index: &ProjectIndex,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    place: &Place,
) -> Result<Type, String> {
    let mut ty = locals[&place.local].ty.clone();
    for segment in &place.projection {
        match segment {
            PlaceSegment::DataField { field } => {
                let mut borrowed = false;
                while let Type::Borrow { ty: next_ty, .. } = ty {
                    ty = *next_ty;
                    borrowed = true;
                }

                if let Type::Named { name, parameters } = ty {
                    if let TypeDeclarationTypeI::Data(datai) =
                        &project_index.type_decl(&name).decl_type
                    {
                        if let Some(next_ty) =
                            datai.type_ctor.fields.iter().find_map(|(name, ty)| {
                                if name.name == *field {
                                    let field_ty = replace_type_variables(
                                        ty.clone(),
                                        &datai.type_params,
                                        &parameters,
                                    );

                                    Some(if borrowed {
                                        Type::Borrow {
                                            ty: Box::new(field_ty),
                                            borrow: None,
                                        }
                                    } else {
                                        field_ty
                                    })
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
            PlaceSegment::EnumField { variant, field } => {
                let mut borrowed = false;
                while let Type::Borrow { ty: next_ty, .. } = ty {
                    ty = *next_ty;
                    borrowed = true;
                }

                if let Type::Named { name, parameters } = ty {
                    if let TypeDeclarationTypeI::Enum(enumi) =
                        &project_index.type_decl(&name).decl_type
                    {
                        let variant = enumi
                            .variants
                            .iter()
                            .find(|v| v.name.name == *variant)
                            .unwrap();

                        if let Some(next_ty) =
                            variant.type_ctor.fields.iter().find_map(|(name, ty)| {
                                if name.name == *field {
                                    let field_ty = replace_type_variables(
                                        ty.clone(),
                                        &enumi.type_params,
                                        &parameters,
                                    );

                                    Some(if borrowed {
                                        Type::Borrow {
                                            ty: Box::new(field_ty),
                                            borrow: None,
                                        }
                                    } else {
                                        field_ty
                                    })
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
            PlaceSegment::EnumDiscriminant => todo!(),
            PlaceSegment::Constant => todo!(),
            PlaceSegment::ImplField { field } => {
                let mut borrowed = false;
                while let Type::Borrow { ty: next_ty, .. } = ty {
                    ty = *next_ty;
                    borrowed = true;
                }

                if let Type::Impl { name, parameters } = ty {
                    let aspecti = project_index.aspect(&name);
                    if let Some(next_ty) = aspecti.definitions.iter().find_map(|def| {
                        if def.name.name == *field {
                            let field_ty = replace_type_variables(
                                def.symbol_type.clone(),
                                &aspecti.type_variables,
                                &parameters,
                            );

                            Some(if borrowed {
                                Type::Borrow {
                                    ty: Box::new(field_ty),
                                    borrow: None,
                                }
                            } else {
                                field_ty
                            })
                        } else {
                            None
                        }
                    }) {
                        ty = next_ty;
                    } else {
                        return Err(format!(
                            "tried to access non-existent field {} of type {}",
                            field,
                            Type::Named { name, parameters }
                        ));
                    }
                } else {
                    return Err(format!("tried to access field {} of type {}", field, ty));
                }
            }
        }
    }
    Ok(ty)
}

fn assert_ty_eq(l: Type, r: Type, reason: &str) -> Result<(), String> {
    assert_eq(l.anonymise_borrows(), r.anonymise_borrows(), reason)
}

fn assert_eq<T: Display + PartialEq>(l: T, r: T, reason: &str) -> Result<(), String> {
    if l == r {
        Ok(())
    } else {
        Err(format!("mismatch: {} != {} ({})", l, r, reason))
    }
}

fn validate_stmt(
    project_index: &ProjectIndex,
    local_defs: &BTreeMap<String, DefinitionM>,
    source_file: &SourceFileIdentifier,
    body: &ControlFlowGraph,
    block_id: BasicBlockId,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    statement: &Statement,
) -> Result<(), String> {
    match &statement.kind {
        StatementKind::Assign { target, source } => assert_ty_eq(
            locals[target].ty.clone(),
            rvalue_type(project_index, locals, source)?,
            "assigning variable",
        ),
        StatementKind::AssignPhi { target, phi_cases } => {
            for (source_block, source) in phi_cases {
                // Verify that the source block actually leads to this block.
                let targets = body.basic_blocks[source_block].terminator.kind.targets();
                if !targets.contains(&block_id) {
                    return Err(format!(
                        "{} does not lead to {} (targets were {:?})",
                        source_block, block_id, targets
                    ));
                }
                assert_ty_eq(
                    locals[target].ty.clone(),
                    locals[source].ty.clone(),
                    "assigning variable in phi",
                )?;
            }
            Ok(())
        }
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
                let def = project_index.definition(name);
                replace_type_variables(def.symbol_type.clone(), &def.type_variables, type_variables)
            };
            assert_ty_eq(
                locals[target].ty.clone(),
                expected_type,
                "instancing symbol",
            )
        }
        StatementKind::Apply {
            argument,
            function,
            target,
        } => {
            let argument_type = rvalue_type(project_index, locals, &*argument)?;
            let return_type = locals[target].ty.clone();
            let expected_func_ty = Type::Function(
                Box::new(argument_type.clone()),
                Box::new(return_type.clone()),
            );
            assert_ty_eq(
                rvalue_type(project_index, locals, &*function)?,
                expected_func_ty,
                "function type",
            )
        }
        StatementKind::InvokeFunction { .. } => {
            Err("input mir should not contain function object instructions".to_string())
        }
        StatementKind::ConstructFunctionObject { .. } => {
            Err("input mir should not contain function object instructions".to_string())
        }
        StatementKind::InvokeFunctionObject { .. } => {
            Err("input mir should not contain function object instructions".to_string())
        }
        StatementKind::Drop { .. } => {
            Err("input mir should not contain drop/free instructions".to_string())
        }
        StatementKind::Free { .. } => {
            Err("input mir should not contain drop/free instructions".to_string())
        }
        StatementKind::ConstructData {
            name,
            type_variables,
            variant,
            fields,
            target,
        } => {
            let type_decl = project_index.type_decl(name);
            let (type_ctor, type_params) = match &type_decl.decl_type {
                TypeDeclarationTypeI::Data(datai) => {
                    if variant.is_some() {
                        return Err(format!(
                            "expected no variant name since {} was a data type not an enum",
                            name
                        ));
                    } else {
                        (&datai.type_ctor, &datai.type_params)
                    }
                }
                TypeDeclarationTypeI::Enum(enumi) => {
                    if let Some(variant_name) = variant {
                        if let Some(variant) = enumi
                            .variants
                            .iter()
                            .find(|variant| variant.name.name == *variant_name)
                        {
                            (&variant.type_ctor, &enumi.type_params)
                        } else {
                            return Err(format!(
                                "variant {} did not exist in enum {}",
                                variant_name, name
                            ));
                        }
                    } else {
                        return Err(format!(
                            "expected a variant name since {} was an enum",
                            name
                        ));
                    }
                }
            };

            for (field_name, field_ty) in &type_ctor.fields {
                let source = &fields[&field_name.name];
                let expected_type =
                    replace_type_variables(field_ty.clone(), type_params, type_variables);
                assert_ty_eq(
                    rvalue_type(project_index, locals, source)?,
                    expected_type,
                    &format!("constructing field {}", field_name.name),
                )?;
            }
            let expected_type = Type::Named {
                name: name.clone(),
                parameters: type_variables.clone(),
            };
            assert_ty_eq(
                locals[target].ty.clone(),
                expected_type,
                "constructing aspect impl",
            )
        }
        StatementKind::ConstructImpl {
            aspect,
            type_variables,
            definitions,
            target,
        } => {
            let aspecti = project_index.aspect(aspect);
            for def in &aspecti.definitions {
                let source = definitions[&def.name.name];
                let expected_type = replace_type_variables(
                    def.symbol_type.clone(),
                    &aspecti.type_variables,
                    type_variables,
                );
                assert_ty_eq(
                    locals[&source].ty.clone(),
                    expected_type,
                    &format!("constructing field {}", def.name.name),
                )?;
            }
            let expected_type = Type::Impl {
                name: aspect.clone(),
                parameters: type_variables.clone(),
            };
            assert_ty_eq(
                locals[target].ty.clone(),
                expected_type,
                "constructing aspect impl",
            )
        }
    }
}

fn validate_terminator(
    project_index: &ProjectIndex,
    locals: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    return_type: &Type,
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
        } => {
            let enumi = if let TypeDeclarationTypeI::Enum(enumi) =
                &project_index.type_decl(enum_name).decl_type
            {
                enumi
            } else {
                unreachable!()
            };
            let mut enum_ty = place_type(project_index, locals, enum_place)?;
            for (value, target) in cases {
                if !enumi
                    .variants
                    .iter()
                    .any(|variant| variant.name.name == *value)
                {
                    return Err(format!("variant {} not found in enum {}", value, enum_name));
                }
                if *target <= block_id {
                    return Err(format!(
                        "blocks were not topologically sorted: {} -> {}",
                        block_id, target
                    ));
                }
            }
            if cases.len() != enumi.variants.len() {
                return Err("not all variants were handled".to_string());
            }
            while let Type::Borrow { ty, .. } = enum_ty {
                enum_ty = *ty;
            }
            assert_ty_eq(
                enum_ty,
                Type::Named {
                    name: enum_name.clone(),
                    parameters: enum_parameters.clone(),
                },
                "switch discriminant type",
            )
        }
        TerminatorKind::SwitchConstant {
            place,
            cases,
            default,
        } => {
            let mut constant_ty = place_type(project_index, locals, place)?;
            while let Type::Borrow { ty, .. } = constant_ty {
                constant_ty = *ty;
            }
            let prim = if let Type::Primitive(prim) = constant_ty {
                prim
            } else {
                return Err(format!(
                    "expected primitive type in switch constant terminator, got {}",
                    constant_ty
                ));
            };

            for (value, target) in cases {
                match value {
                    ConstantValue::Unit => {
                        assert_eq(prim, PrimitiveType::Unit, "switch constant type")?
                    }
                    ConstantValue::Bool(_) => {
                        assert_eq(prim, PrimitiveType::Bool, "switch constant type")?
                    }
                    ConstantValue::Int(_) => {
                        assert_eq(prim, PrimitiveType::Int, "switch constant type")?
                    }
                }
                if *target <= block_id {
                    return Err(format!(
                        "blocks were not topologically sorted: {} -> {}",
                        block_id, target
                    ));
                }
            }

            if *default <= block_id {
                Err(format!(
                    "blocks were not topologically sorted: {} -> {}",
                    block_id, default
                ))
            } else {
                Ok(())
            }
        }
        TerminatorKind::Invalid => Err("unreachable terminator".to_string()),
        TerminatorKind::Return { value } => {
            assert_ty_eq(locals[value].ty.clone(), return_type.clone(), "return type")
        }
    }
}
