use std::collections::{BTreeMap, HashMap};

use inkwell::{types::BasicType, values::PointerValue, AddressSpace};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_mir::{LocalVariableInfo, LocalVariableName, Operand, PlaceSegment, Rvalue};
use quill_parser::ConstantValue;
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::CodeGenContext,
    repr::{MonomorphisationParameters, MonomorphisedType, Representations},
};

/// Returns None if the rvalue had no representation.
pub fn get_pointer_to_rvalue<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    index: &ProjectIndex,
    reprs: &Representations<'_, 'ctx>,
    locals: &HashMap<LocalVariableName, PointerValue<'ctx>>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Option<PointerValue<'ctx>> {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => {
            if let Some(mut ptr) = locals.get(&place.local).copied() {
                let mut rvalue_ty = local_variable_names[&place.local].ty.clone();

                for segment in place.projection.clone() {
                    match segment {
                        PlaceSegment::DataField { field } => {
                            // rvalue_ty is a data type.
                            if let Type::Named { name, parameters } = rvalue_ty {
                                let decl = &index[&name.source_file].types[&name.name];
                                if let TypeDeclarationTypeI::Data(datai) = &decl.decl_type {
                                    rvalue_ty = datai
                                        .type_ctor
                                        .fields
                                        .iter()
                                        .find_map(|(field_name, field_type)| {
                                            if field_name.name == field {
                                                Some(replace_type_variables(
                                                    field_type.clone(),
                                                    &datai.type_params,
                                                    &parameters,
                                                ))
                                            } else {
                                                None
                                            }
                                        })
                                        .unwrap();
                                } else {
                                    unreachable!()
                                }

                                let data = reprs
                                    .get_data(&MonomorphisedType {
                                        name,
                                        mono: MonomorphisationParameters {
                                            type_parameters: parameters,
                                        },
                                    })
                                    .unwrap();
                                ptr = data.load(codegen, reprs, ptr, &field).unwrap();
                            } else {
                                unreachable!()
                            }
                        }
                        PlaceSegment::EnumField { variant, field } => {
                            // rvalue_ty is an enum type.
                            if let Type::Named { name, parameters } = rvalue_ty {
                                let decl = &index[&name.source_file].types[&name.name];
                                if let TypeDeclarationTypeI::Enum(enumi) = &decl.decl_type {
                                    rvalue_ty = enumi
                                        .variants
                                        .iter()
                                        .find(|the_variant| the_variant.name.name == variant)
                                        .unwrap()
                                        .type_ctor
                                        .fields
                                        .iter()
                                        .find_map(|(field_name, field_type)| {
                                            if field_name.name == field {
                                                Some(replace_type_variables(
                                                    field_type.clone(),
                                                    &enumi.type_params,
                                                    &parameters,
                                                ))
                                            } else {
                                                None
                                            }
                                        })
                                        .unwrap();
                                } else {
                                    unreachable!()
                                }

                                let the_enum = reprs
                                    .get_enum(&MonomorphisedType {
                                        name,
                                        mono: MonomorphisationParameters {
                                            type_parameters: parameters,
                                        },
                                    })
                                    .unwrap();
                                ptr = the_enum
                                    .load(codegen, reprs, ptr, &variant, &field)
                                    .unwrap();
                            } else {
                                unreachable!()
                            }
                        }
                        PlaceSegment::EnumDiscriminant => {
                            // rvalue_ty is an enum type.
                            if let Type::Named { name, parameters } = rvalue_ty {
                                rvalue_ty = Type::Primitive(PrimitiveType::Int);
                                let the_enum = reprs
                                    .get_enum(&MonomorphisedType {
                                        name,
                                        mono: MonomorphisationParameters {
                                            type_parameters: parameters,
                                        },
                                    })
                                    .unwrap();
                                ptr = the_enum.get_discriminant(codegen, ptr);
                            } else {
                                unreachable!()
                            }
                        }
                    }
                }

                Some(ptr)
            } else {
                None
            }
        }
        Rvalue::Borrow(local) => {
            // Return a pointer to the given local variable.
            Some(locals[local])
        }
        Rvalue::Use(Operand::Constant(constant)) => {
            // Alloca the constant, then make a pointer to it.
            match constant {
                ConstantValue::Unit => unreachable!(),
                ConstantValue::Bool(value) => {
                    let mem = codegen
                        .builder
                        .build_alloca(codegen.context.bool_type(), "constant");
                    codegen.builder.build_store(
                        mem,
                        codegen
                            .context
                            .bool_type()
                            .const_int(if *value { 1 } else { 0 }, true),
                    );
                    Some(mem)
                }
                ConstantValue::Int(value) => {
                    let mem = codegen
                        .builder
                        .build_alloca(codegen.context.i64_type(), "constant");
                    codegen.builder.build_store(
                        mem,
                        codegen
                            .context
                            .i64_type()
                            .const_int(unsafe { std::mem::transmute::<i64, u64>(*value) }, true),
                    );
                    Some(mem)
                }
            }
        }
    }
}

/// Returns the type of the given rvalue.
pub fn get_type_of_rvalue(
    index: &ProjectIndex,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Type {
    match rvalue {
        Rvalue::Use(Operand::Move(place)) | Rvalue::Use(Operand::Copy(place)) => {
            let mut rvalue_ty = local_variable_names[&place.local].ty.clone();

            for segment in place.projection.clone() {
                match segment {
                    PlaceSegment::DataField { field } => {
                        // rvalue_ty is a data type.
                        if let Type::Named { name, parameters } = rvalue_ty {
                            let decl = &index[&name.source_file].types[&name.name];
                            if let TypeDeclarationTypeI::Data(datai) = &decl.decl_type {
                                rvalue_ty = datai
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .find_map(|(field_name, field_type)| {
                                        if field_name.name == field {
                                            Some(replace_type_variables(
                                                field_type.clone(),
                                                &datai.type_params,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                    .unwrap();
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    PlaceSegment::EnumField { variant, field } => {
                        // rvalue_ty is an enum type.
                        if let Type::Named { name, parameters } = rvalue_ty {
                            let decl = &index[&name.source_file].types[&name.name];
                            if let TypeDeclarationTypeI::Enum(enumi) = &decl.decl_type {
                                rvalue_ty = enumi
                                    .variants
                                    .iter()
                                    .find(|the_variant| the_variant.name.name == variant)
                                    .unwrap()
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .find_map(|(field_name, field_type)| {
                                        if field_name.name == field {
                                            Some(replace_type_variables(
                                                field_type.clone(),
                                                &enumi.type_params,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                    .unwrap();
                            } else {
                                unreachable!()
                            }
                        } else {
                            unreachable!()
                        }
                    }
                    PlaceSegment::EnumDiscriminant => {
                        // rvalue_ty is an enum type.
                        if let Type::Named { .. } = rvalue_ty {
                            rvalue_ty = Type::Primitive(PrimitiveType::Int);
                        } else {
                            unreachable!()
                        }
                    }
                }
            }

            rvalue_ty
        }
        Rvalue::Borrow(local) => {
            // Return a pointer to the given local variable.
            Type::Borrow {
                ty: Box::new(local_variable_names[local].ty.clone()),
                borrow: None,
            }
        }
        Rvalue::Use(Operand::Constant(constant)) => {
            // Alloca the constant, then make a pointer to it.
            match constant {
                ConstantValue::Unit => Type::Primitive(PrimitiveType::Unit),
                ConstantValue::Bool(_) => Type::Primitive(PrimitiveType::Bool),
                ConstantValue::Int(_) => Type::Primitive(PrimitiveType::Int),
            }
        }
    }
}

/// Sometimes a value is unacceptable in its current form to be used as a function argument.
/// For instance, a function object may have a specific known type, but it must be first "anonymised"
/// into the `fobj*` type in order to then be passed into a function.
/// This function gets the rvalue, then bitcasts it to the correct type if required.
pub fn get_pointer_to_rvalue_arg<'ctx>(
    codegen: &CodeGenContext<'ctx>,
    index: &ProjectIndex,
    reprs: &Representations<'_, 'ctx>,
    locals: &HashMap<LocalVariableName, PointerValue<'ctx>>,
    local_variable_names: &BTreeMap<LocalVariableName, LocalVariableInfo>,
    rvalue: &Rvalue,
) -> Option<PointerValue<'ctx>> {
    if let Some(ptr) =
        get_pointer_to_rvalue(codegen, index, reprs, locals, local_variable_names, rvalue)
    {
        let ty = get_type_of_rvalue(index, local_variable_names, rvalue);
        if let Type::Function(_, _) = ty {
            // This is a function object, so we need to bitcast it to a generic `fobj**`.
            // The double pointer is expected; we want to return a *pointer* to an rvalue.
            Some(
                codegen
                    .builder
                    .build_bitcast(
                        ptr,
                        reprs
                            .general_func_obj_ty
                            .llvm_type
                            .ptr_type(AddressSpace::Generic),
                        "as_fobj",
                    )
                    .into_pointer_value(),
            )
        } else {
            Some(ptr)
        }
    } else {
        None
    }
}
