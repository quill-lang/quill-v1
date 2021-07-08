use std::{
    collections::{BTreeMap, HashMap},
    ops::Deref,
};

use inkwell::{types::BasicType, values::PointerValue, AddressSpace};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_mir::mir::{LocalVariableInfo, LocalVariableName, PlaceSegment, Rvalue};
use quill_parser::expr_pat::ConstantValue;
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::CodeGenContext,
    monomorphisation::{MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType},
    repr::Representations,
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
        Rvalue::Move(place) => {
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
                            // rvalue_ty is an enum type, or a borrow of an enum type.
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
                            } else if let Type::Borrow { ty, .. } = rvalue_ty {
                                // We don't need to explicitly dereference the borrow, since borrowed values and
                                // owned values are both represented as pointers to an alloca in LLVM IR.
                                if let Type::Named { name, parameters } = *ty {
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
                            } else {
                                unreachable!()
                            }
                        }
                        PlaceSegment::ImplField { field } => {
                            // rvalue_ty is an impl of an aspect.
                            if let Type::Impl { name, parameters } = rvalue_ty {
                                let aspect = &index[&name.source_file].aspects[&name.name];

                                rvalue_ty = aspect
                                    .definitions
                                    .iter()
                                    .find_map(|def| {
                                        if def.name.name == field {
                                            Some(replace_type_variables(
                                                def.symbol_type.clone(),
                                                &def.type_variables,
                                                &parameters,
                                            ))
                                        } else {
                                            None
                                        }
                                    })
                                    .unwrap();

                                let data = reprs
                                    .get_aspect(&MonomorphisedAspect {
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
                    }
                }

                Some(ptr)
            } else {
                None
            }
        }
        Rvalue::Borrow(local) => {
            // Return a pointer to the given local variable.
            // Note that since local variables are stored using `alloca` instructions,
            // this will return a *double pointer*:
            // a pointer to the place on the stack (a pointer) that the object is stored.
            let ptr = codegen
                .builder
                .build_alloca(locals[local].get_type(), "borrow");
            codegen.builder.build_store(ptr, locals[local]);
            Some(ptr)
        }
        Rvalue::Copy(local) => {
            // Call the copy function for this local variable, which is a borrow of some type.
            // First, deduce the type of this local.
            let ty = if let Type::Borrow { ty, .. } = &local_variable_names[local].ty {
                ty
            } else {
                unreachable!()
            };

            match ty.deref() {
                Type::Named { name, parameters } => {
                    // Call the copy function for this type.
                    todo!()
                }
                Type::Variable {
                    variable,
                    parameters,
                } => todo!(),
                Type::Function(_, _) => {
                    // This is a function object.
                    todo!()
                }
                Type::Primitive(ty) => {
                    // Primitive types can simply be copied bitwise.
                    match ty {
                        PrimitiveType::Unit => None,
                        PrimitiveType::Bool => {
                            let ptr = codegen
                                .builder
                                .build_alloca(codegen.context.bool_type(), "copied_value");
                            let ptr_to_value = codegen
                                .builder
                                .build_load(locals[local], "value_to_copy_ptr")
                                .into_pointer_value();
                            let value = codegen.builder.build_load(ptr_to_value, "value_to_copy");
                            codegen.builder.build_store(ptr, value);
                            Some(ptr)
                        }
                        PrimitiveType::Int => {
                            let ptr = codegen
                                .builder
                                .build_alloca(codegen.context.i64_type(), "copied_value");
                            let ptr_to_value = codegen
                                .builder
                                .build_load(locals[local], "value_to_copy_ptr")
                                .into_pointer_value();
                            let value = codegen.builder.build_load(ptr_to_value, "value_to_copy");
                            codegen.builder.build_store(ptr, value);
                            Some(ptr)
                        }
                    }
                }
                Type::Borrow { ty, borrow } => todo!(),
                Type::Impl { name, parameters } => todo!(),
            }
        }
        Rvalue::Constant(constant) => {
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
        Rvalue::Move(place) => {
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
                    PlaceSegment::ImplField { .. } => todo!(),
                }
            }

            rvalue_ty
        }
        Rvalue::Copy(local) => {
            // Return the dereferenced type of the given local variable.
            if let Type::Borrow { ty, .. } = local_variable_names[local].ty.clone() {
                *ty
            } else {
                panic!("type was {}", local_variable_names[local].ty)
            }
        }
        Rvalue::Borrow(local) => {
            // Return a pointer to the given local variable.
            Type::Borrow {
                ty: Box::new(local_variable_names[local].ty.clone()),
                borrow: None,
            }
        }
        Rvalue::Constant(constant) => {
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
