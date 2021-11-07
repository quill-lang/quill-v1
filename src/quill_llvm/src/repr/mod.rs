use std::{collections::BTreeMap, convert::TryFrom};

use inkwell::{
    debug_info::{AsDIScope, DIDerivedType, DIFlagsConstants},
    types::{BasicType, BasicTypeEnum},
    values::{BasicValueEnum, CallableValue, PointerValue},
    AddressSpace,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_reprs::{data::FieldIndex, sort_types::MonomorphisedItem, Representations};
use quill_type::{PrimitiveType, Type};

use crate::codegen::CodeGenContext;
use quill_monomorphise::monomorphisation::{
    FunctionObjectDescriptor, MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType,
};

use self::{
    any_type::AnyTypeRepresentation,
    data::{LLVMDataRepresentation, LLVMEnumRepresentation},
};

pub mod any_type;
pub mod data;
pub mod llvm_struct;

/// Stores the LLVM-specific representations of all data/struct types in a project, post monomorphisation.
pub struct LLVMRepresentations<'a, 'ctx> {
    pub codegen: &'a CodeGenContext<'ctx>,
    datas: BTreeMap<MonomorphisedType, LLVMDataRepresentation<'ctx>>,
    enums: BTreeMap<MonomorphisedType, LLVMEnumRepresentation<'ctx>>,
    func_objects: BTreeMap<FunctionObjectDescriptor, LLVMDataRepresentation<'ctx>>,
    /// The representation of an arbitrary impl for a given aspect.
    aspects: BTreeMap<MonomorphisedAspect, LLVMDataRepresentation<'ctx>>,
    /// Use this type for a general function object that you don't know the type of.
    pub general_func_obj_ty: AnyTypeRepresentation<'ctx>,
}

impl<'a, 'ctx> LLVMRepresentations<'a, 'ctx> {
    pub fn new(
        index: &ProjectIndex,
        codegen: &'a CodeGenContext<'ctx>,
        prev_reprs: Representations,
    ) -> Self {
        let general_func_obj_ty = codegen.context.opaque_struct_type("fobj");
        general_func_obj_ty.set_body(
            &[
                // The function ptr to call
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
                // The copy function
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
                // The drop function
                codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
            ],
            false,
        );

        let mut reprs = Self {
            codegen,
            datas: BTreeMap::new(),
            enums: BTreeMap::new(),
            func_objects: BTreeMap::new(),
            aspects: BTreeMap::new(),
            general_func_obj_ty: AnyTypeRepresentation::new(
                codegen,
                general_func_obj_ty.ptr_type(AddressSpace::Generic).into(),
                codegen
                    .di_builder
                    .create_basic_type(
                        "<function object>",
                        codegen
                            .target_data()
                            .get_bit_size(&general_func_obj_ty.ptr_type(AddressSpace::Generic)),
                        1,
                        DIFlagsConstants::PUBLIC,
                    )
                    .unwrap()
                    .as_type(),
            ),
        };

        for mono_ty in prev_reprs.sorted_types.iter().cloned() {
            match mono_ty.ty {
                MonomorphisedItem::Type(ty) => {
                    let decl = index.type_decl(&ty.name);
                    match &decl.decl_type {
                        TypeDeclarationTypeI::Data(_) => {
                            let repr = prev_reprs.get_data(&ty).unwrap();
                            reprs
                                .datas
                                .insert(ty, LLVMDataRepresentation::new(&reprs, repr));
                        }
                        TypeDeclarationTypeI::Enum(_) => {
                            let repr = prev_reprs.get_enum(&ty).unwrap();
                            reprs
                                .enums
                                .insert(ty, LLVMEnumRepresentation::new(&reprs, repr));
                        }
                    };
                }
                MonomorphisedItem::Aspect(asp) => {
                    let repr = prev_reprs.get_aspect(&asp).unwrap();
                    reprs
                        .aspects
                        .insert(asp, LLVMDataRepresentation::new(&reprs, repr));
                }
            }
        }

        reprs.create_drop_copy_funcs();

        reprs
    }

    /// If the given type needs no representation, None is returned.
    pub fn repr(&self, ty: Type) -> Option<AnyTypeRepresentation<'ctx>> {
        match ty {
            Type::Named { name, parameters } => {
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if let Some(repr) = self.datas.get(&mono_ty) {
                    repr.llvm_repr.as_ref().map(|llvm_repr| {
                        AnyTypeRepresentation::new_with_alignment(
                            BasicTypeEnum::StructType(llvm_repr.ty),
                            repr.di_type.as_type(),
                            llvm_repr.abi_alignment,
                        )
                    })
                } else if let Some(repr) = self.enums.get(&mono_ty) {
                    Some(AnyTypeRepresentation::new_with_alignment(
                        BasicTypeEnum::StructType(repr.llvm_repr.ty),
                        repr.di_type,
                        repr.llvm_repr.abi_alignment,
                    ))
                } else {
                    unreachable!("ty was {}", mono_ty)
                }
            }
            Type::Variable { .. } => unreachable!(),
            Type::Function(_, _) => {
                // This is a function object.
                Some(self.general_func_obj_ty)
            }
            Type::Primitive(PrimitiveType::Unit) => None,
            Type::Primitive(PrimitiveType::Bool) => Some(AnyTypeRepresentation::new(
                self.codegen,
                BasicTypeEnum::IntType(self.codegen.context.bool_type()),
                self.codegen
                    .di_builder
                    .create_basic_type("Bool", 1, 2, DIFlagsConstants::PUBLIC)
                    .unwrap()
                    .as_type(),
            )),
            Type::Primitive(PrimitiveType::Int) => Some(AnyTypeRepresentation::new(
                self.codegen,
                BasicTypeEnum::IntType(self.codegen.context.i64_type()),
                self.codegen
                    .di_builder
                    .create_basic_type("Int", 64, 5, DIFlagsConstants::PUBLIC)
                    .unwrap()
                    .as_type(),
            )),
            Type::Primitive(PrimitiveType::Char) => Some(AnyTypeRepresentation::new(
                // Represented as an unsigned char in DWARF.
                self.codegen,
                BasicTypeEnum::IntType(self.codegen.context.i32_type()),
                self.codegen
                    .di_builder
                    .create_basic_type("Char", 32, 8, DIFlagsConstants::PUBLIC)
                    .unwrap()
                    .as_type(),
            )),
            Type::Borrow { ty, .. } => self.repr(*ty).map(|repr| {
                AnyTypeRepresentation::new(
                    self.codegen,
                    repr.llvm_type.ptr_type(AddressSpace::Generic).into(),
                    // TODO manage this pointer type
                    repr.di_type,
                )
            }),
            Type::Impl { name, parameters } => {
                let mono_asp = MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if let Some(repr) = self.aspects.get(&mono_asp) {
                    repr.llvm_repr.as_ref().map(|llvm_repr| {
                        AnyTypeRepresentation::new_with_alignment(
                            BasicTypeEnum::StructType(llvm_repr.ty),
                            repr.di_type.as_type(),
                            llvm_repr.abi_alignment,
                        )
                    })
                } else {
                    unreachable!("ty was {}", mono_asp)
                }
            }
        }
    }

    pub fn get_data(
        &self,
        descriptor: &MonomorphisedType,
    ) -> Option<&LLVMDataRepresentation<'ctx>> {
        self.datas.get(descriptor)
    }

    pub fn get_enum(
        &self,
        descriptor: &MonomorphisedType,
    ) -> Option<&LLVMEnumRepresentation<'ctx>> {
        self.enums.get(descriptor)
    }

    pub fn get_fobj(
        &self,
        descriptor: &FunctionObjectDescriptor,
    ) -> Option<&LLVMDataRepresentation<'ctx>> {
        self.func_objects.get(descriptor)
    }

    pub fn insert_fobj(
        &mut self,
        descriptor: FunctionObjectDescriptor,
        fobj: LLVMDataRepresentation<'ctx>,
    ) {
        self.func_objects.insert(descriptor, fobj);
    }

    pub fn get_aspect(
        &self,
        descriptor: &MonomorphisedAspect,
    ) -> Option<&LLVMDataRepresentation<'ctx>> {
        self.aspects.get(descriptor)
    }

    /// Drops a value of the given type behind the given pointer.
    pub fn drop_ptr(&self, ty: Type, variable_ptr: PointerValue<'ctx>) {
        match ty.clone() {
            Type::Named { name, parameters } => {
                // We need to call this type's drop function.
                let repr = self.repr(ty);
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", mono_ty))
                    .unwrap();
                if repr.is_some() {
                    let variable = self
                        .codegen
                        .builder
                        .build_load(variable_ptr, "value_to_drop");
                    self.codegen.builder.build_call(
                        func,
                        &[variable.into()],
                        &format!("drop_{}", mono_ty),
                    );
                } else {
                    self.codegen
                        .builder
                        .build_call(func, &[], &format!("drop_{}", mono_ty));
                }
            }
            Type::Variable { .. } => {
                // We've already monomorphised all type variables into concrete types, so this should never happen.
                unreachable!()
            }
            Type::Function(_, _) => {
                let func_object_ptr = self
                    .codegen
                    .builder
                    .build_load(variable_ptr, "fobj_loaded")
                    .into_pointer_value();
                // Get the third element of this function object, which is the drop function.
                let fptr_raw = self
                    .codegen
                    .builder
                    .build_struct_gep(func_object_ptr, 2, "drop_raw_ptr")
                    .unwrap();
                let fptr_raw = self.codegen.builder.build_load(fptr_raw, "drop_raw");
                let fptr = self
                    .codegen
                    .builder
                    .build_bitcast(
                        fptr_raw,
                        self.codegen
                            .context
                            .void_type()
                            .fn_type(
                                &[BasicTypeEnum::try_from(
                                    variable_ptr.get_type().get_element_type(),
                                )
                                .unwrap()
                                .into()],
                                false,
                            )
                            .ptr_type(AddressSpace::Generic),
                        "drop",
                    )
                    .into_pointer_value();

                let args = &[self
                    .codegen
                    .builder
                    .build_bitcast(
                        func_object_ptr,
                        self.general_func_obj_ty.llvm_type,
                        "fobj_bitcast",
                    )
                    .into()];

                self.codegen.builder.build_call(
                    CallableValue::try_from(fptr).unwrap(),
                    args,
                    "drop_call",
                );
            }
            Type::Primitive(_) => {
                // No operation is required.
            }
            Type::Borrow { .. } => {
                // Dropping a borrow does nothing. No operation is required.
            }
            Type::Impl { name, parameters } => {
                // We need to call this type's drop function.
                let repr = self.repr(ty);
                let mono_asp = MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", mono_asp))
                    .unwrap();
                if repr.is_some() {
                    let variable = self
                        .codegen
                        .builder
                        .build_load(variable_ptr, "value_to_drop");
                    self.codegen.builder.build_call(
                        func,
                        &[variable.into()],
                        &format!("drop_{}", mono_asp),
                    );
                } else {
                    self.codegen
                        .builder
                        .build_call(func, &[], &format!("drop_{}", mono_asp));
                }
            }
        }
    }

    /// Copies a value of the given type behind the given (single) pointer.
    /// The result is the copy of the value if the type had a representation, given as a direct value (not an alloca).
    pub fn copy_ptr(
        &self,
        ty: Type,
        variable_ptr: PointerValue<'ctx>,
    ) -> Option<BasicValueEnum<'ctx>> {
        match ty.clone() {
            Type::Named { name, parameters } => {
                // Call the copy function for this type.
                let repr = self.repr(ty);
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if repr.is_some() {
                    let function = self
                        .codegen
                        .module
                        .get_function(&format!("copy/{}", mono_ty))
                        .unwrap();
                    self.codegen
                        .builder
                        .build_call(function, &[variable_ptr.into()], "copied_value")
                        .try_as_basic_value()
                        .left()
                } else {
                    None
                }
            }
            Type::Variable { .. } => {
                panic!("shouldn't still have type variables at this point")
            }
            Type::Function(_, _) => {
                // This is a function object. Specifically, a `fobj**`.
                // The output value should just be an `fobj*`.
                let fobj = self
                    .codegen
                    .builder
                    .build_load(variable_ptr, "loaded_fobj")
                    .into_pointer_value();
                // The `copy` function is the second field of the function object.
                let copy = self
                    .codegen
                    .builder
                    .build_struct_gep(fobj, 1, "loaded_copy_fn_ptr")
                    .unwrap();
                let copy = self.codegen.builder.build_load(copy, "loaded_copy_fn");
                let copy = self
                    .codegen
                    .builder
                    .build_bitcast(
                        copy,
                        self.general_func_obj_ty
                            .llvm_type
                            .fn_type(&[self.general_func_obj_ty.llvm_type.into()], false)
                            .ptr_type(AddressSpace::Generic),
                        "fptr",
                    )
                    .into_pointer_value();

                // Invoke this function.
                let result = self.codegen.builder.build_call(
                    CallableValue::try_from(copy).unwrap(),
                    &[fobj.into()],
                    "copied_fobj",
                );
                result.try_as_basic_value().left()
            }
            Type::Primitive(ty) => {
                // Primitive types can simply be copied bitwise.
                match ty {
                    PrimitiveType::Unit => None,
                    PrimitiveType::Bool | PrimitiveType::Int | PrimitiveType::Char => Some(
                        self.codegen
                            .builder
                            .build_load(variable_ptr, "copied_value"),
                    ),
                }
            }
            Type::Borrow { .. } => {
                // Borrows can be trivially copied.
                // The validity of the borrow has already been checked by the borrow checker.
                Some(
                    self.codegen
                        .builder
                        .build_load(variable_ptr, "copied_value"),
                )
            }
            Type::Impl { name, parameters } => {
                // Call the copy function for this type.
                let repr = self.repr(ty);
                let mono_asp = MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if repr.is_some() {
                    let function = self
                        .codegen
                        .module
                        .get_function(&format!("copy/{}", mono_asp))
                        .unwrap();
                    self.codegen
                        .builder
                        .build_call(function, &[variable_ptr.into()], "copied_value")
                        .try_as_basic_value()
                        .left()
                } else {
                    None
                }
            }
        }
    }

    /// Create a `drop` and `copy` function for each type.
    /// These functions are guaranteed to be free of side effects and cannot be overridden inside Quill.
    fn create_drop_copy_funcs(&self) {
        // First, declare all the function signatures.
        for (ty, repr) in &self.datas {
            self.codegen.module.add_function(
                &format!("drop/{}", ty),
                if let Some(llvm_repr) = &repr.llvm_repr {
                    self.codegen
                        .context
                        .void_type()
                        .fn_type(&[llvm_repr.ty.into()], false)
                } else {
                    self.codegen.context.void_type().fn_type(&[], false)
                },
                None,
            );
            self.codegen.module.add_function(
                &format!("copy/{}", ty),
                if let Some(llvm_repr) = &repr.llvm_repr {
                    llvm_repr.ty.fn_type(
                        &[llvm_repr.ty.ptr_type(AddressSpace::Generic).into()],
                        false,
                    )
                } else {
                    self.codegen.context.void_type().fn_type(&[], false)
                },
                None,
            );
        }
        for (ty, repr) in &self.enums {
            self.codegen.module.add_function(
                &format!("drop/{}", ty),
                self.codegen
                    .context
                    .void_type()
                    .fn_type(&[repr.llvm_repr.ty.into()], false),
                None,
            );
            self.codegen.module.add_function(
                &format!("copy/{}", ty),
                repr.llvm_repr.ty.fn_type(
                    &[repr.llvm_repr.ty.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                None,
            );
        }
        for (ty, repr) in &self.aspects {
            self.codegen.module.add_function(
                &format!("drop/{}", ty),
                if let Some(llvm_repr) = &repr.llvm_repr {
                    self.codegen
                        .context
                        .void_type()
                        .fn_type(&[llvm_repr.ty.into()], false)
                } else {
                    self.codegen.context.void_type().fn_type(&[], false)
                },
                None,
            );
            self.codegen.module.add_function(
                &format!("copy/{}", ty),
                if let Some(llvm_repr) = &repr.llvm_repr {
                    llvm_repr.ty.fn_type(
                        &[llvm_repr.ty.ptr_type(AddressSpace::Generic).into()],
                        false,
                    )
                } else {
                    self.codegen.context.void_type().fn_type(&[], false)
                },
                None,
            );
        }

        // Now, implement the functions.
        for (ty, repr) in &self.datas {
            // Generate the drop function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "drop");
                self.codegen.builder.position_at_end(block);

                if repr.llvm_repr.is_some() {
                    let value = func.get_first_param().unwrap();
                    let ptr = self
                        .codegen
                        .builder
                        .build_alloca(value.get_type(), "value_to_drop");
                    self.codegen.builder.build_store(ptr, value);

                    for heap_field in repr.field_names_on_heap() {
                        let ptr_to_field = repr.load(self.codegen, self, ptr, heap_field).unwrap();
                        let ty = repr.field_ty(heap_field).unwrap().clone();
                        self.drop_ptr(ty, ptr_to_field);
                    }

                    repr.free_fields(self.codegen, ptr);
                }

                self.codegen.builder.build_return(None);
            }

            // Generate the copy function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("copy/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "copy");
                self.codegen.builder.position_at_end(block);

                if let Some(llvm_repr) = &repr.llvm_repr {
                    let source = func.get_first_param().unwrap().into_pointer_value();
                    let ptr = self
                        .codegen
                        .builder
                        .build_alloca(llvm_repr.ty, "return_value");

                    // Copy each field over into the new value.
                    // Start by allocating sufficient space on the heap for the new values.
                    repr.malloc_fields(self.codegen, self, ptr);

                    // Now, for each field, copy it over.
                    for field_name in repr.field_indices().keys() {
                        // Get the field from the source.
                        if let Some(source_field) =
                            repr.load(self.codegen, self, source, field_name)
                        {
                            // Copy the field.
                            let source_field_copied = self
                                .copy_ptr(repr.field_ty(field_name).unwrap().clone(), source_field)
                                .unwrap();
                            repr.store(self.codegen, self, ptr, source_field_copied, field_name);
                        }
                    }

                    self.codegen.builder.build_return(Some(
                        &self.codegen.builder.build_load(ptr, "return_value_deref"),
                    ));
                } else {
                    self.codegen.builder.build_return(None);
                }
            }
        }

        for (ty, repr) in &self.enums {
            // Generate the drop function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "drop");
                self.codegen.builder.position_at_end(block);

                let value = func.get_first_param().unwrap();
                let ptr = self
                    .codegen
                    .builder
                    .build_alloca(value.get_type(), "value_to_drop");
                self.codegen.builder.build_store(ptr, value);

                // Switch on the discriminant to see what needs dropping.
                let disc = repr.get_discriminant(self.codegen, ptr);
                let disc_loaded = self
                    .codegen
                    .builder
                    .build_load(disc, "discriminant")
                    .into_int_value();

                // Build the blocks for each case.
                let mut cases = Vec::new();
                for (discriminant, int_value) in &repr.variant_discriminants {
                    let block = self
                        .codegen
                        .context
                        .insert_basic_block_after(block, &format!("discriminant_{}", int_value));
                    cases.push((
                        self.codegen.context.i64_type().const_int(*int_value, false),
                        block,
                    ));
                    self.codegen.builder.position_at_end(block);
                    let variant = &repr.variants[discriminant];
                    let variable = self
                        .codegen
                        .builder
                        .build_bitcast(
                            ptr,
                            variant
                                .llvm_repr
                                .as_ref()
                                .unwrap()
                                .ty
                                .ptr_type(AddressSpace::Generic),
                            &format!("as_{}", discriminant),
                        )
                        .into_pointer_value();
                    for heap_field in variant.field_names_on_heap() {
                        let ptr_to_field = variant
                            .load(self.codegen, self, variable, heap_field)
                            .unwrap();
                        let ty = variant.field_ty(heap_field).unwrap().clone();
                        self.drop_ptr(ty, ptr_to_field);
                    }
                    variant.free_fields(self.codegen, variable);
                    self.codegen.builder.build_return(None);
                }

                self.codegen.builder.position_at_end(block);
                self.codegen
                    .builder
                    .build_switch(disc_loaded, cases[0].1, &cases);
            }

            // Generate the copy function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("copy/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "copy");
                self.codegen.builder.position_at_end(block);

                let ptr = func.get_first_param().unwrap().into_pointer_value();

                // Switch on the discriminant to see what needs copying.
                let disc = repr.get_discriminant(self.codegen, ptr);
                let disc_loaded = self
                    .codegen
                    .builder
                    .build_load(disc, "discriminant")
                    .into_int_value();

                // Build the blocks for each case.
                let mut cases = Vec::new();
                for (discriminant, int_value) in &repr.variant_discriminants {
                    let block = self
                        .codegen
                        .context
                        .insert_basic_block_after(block, &format!("discriminant_{}", int_value));
                    cases.push((
                        self.codegen.context.i64_type().const_int(*int_value, false),
                        block,
                    ));
                    self.codegen.builder.position_at_end(block);
                    let variant = &repr.variants[discriminant];
                    let source = self
                        .codegen
                        .builder
                        .build_bitcast(
                            ptr,
                            variant
                                .llvm_repr
                                .as_ref()
                                .unwrap()
                                .ty
                                .ptr_type(AddressSpace::Generic),
                            &format!("as_{}", discriminant),
                        )
                        .into_pointer_value();

                    if let Some(llvm_repr) = &variant.llvm_repr {
                        let ptr = self
                            .codegen
                            .builder
                            .build_alloca(llvm_repr.ty, "return_value");

                        // Copy each field over into the new value.
                        // Start by allocating sufficient space on the heap for the new values.
                        variant.malloc_fields(self.codegen, self, ptr);

                        // Now, for each field, copy it over.
                        for field_name in variant.field_indices().keys() {
                            // Get the field from the source.
                            if let Some(source_field) =
                                variant.load(self.codegen, self, source, field_name)
                            {
                                // Copy the field.
                                let source_field_copied = self
                                    .copy_ptr(
                                        variant.field_ty(field_name).unwrap().clone(),
                                        source_field,
                                    )
                                    .unwrap();
                                variant.store(
                                    self.codegen,
                                    self,
                                    ptr,
                                    source_field_copied,
                                    field_name,
                                );
                            }
                        }

                        // Finally, bitcast this specific variant to the enum's representation.
                        let ptr = self
                            .codegen
                            .builder
                            .build_bitcast(
                                ptr,
                                repr.llvm_repr.ty.ptr_type(AddressSpace::Generic),
                                "return_value_bitcast",
                            )
                            .into_pointer_value();

                        self.codegen.builder.build_return(Some(
                            &self.codegen.builder.build_load(ptr, "return_value_deref"),
                        ));
                    } else {
                        self.codegen.builder.build_return(None);
                    }
                }

                self.codegen.builder.position_at_end(block);
                self.codegen
                    .builder
                    .build_switch(disc_loaded, cases[0].1, &cases);
            }
        }

        for (ty, repr) in &self.aspects {
            // Generate the drop function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "drop");
                self.codegen.builder.position_at_end(block);

                if repr.llvm_repr.is_some() {
                    let value = func.get_first_param().unwrap();
                    let ptr = self
                        .codegen
                        .builder
                        .build_alloca(value.get_type(), "value_to_drop");
                    self.codegen.builder.build_store(ptr, value);

                    for heap_field in repr.field_names_on_heap() {
                        let ptr_to_field = repr.load(self.codegen, self, ptr, heap_field).unwrap();
                        let ty = repr.field_ty(heap_field).unwrap().clone();
                        self.drop_ptr(ty, ptr_to_field);
                    }

                    repr.free_fields(self.codegen, ptr);
                }

                self.codegen.builder.build_return(None);
            }

            // Generate the copy function.
            {
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("copy/{}", ty))
                    .unwrap();

                let block = self.codegen.context.append_basic_block(func, "copy");
                self.codegen.builder.position_at_end(block);

                if let Some(llvm_repr) = &repr.llvm_repr {
                    let source = func.get_first_param().unwrap().into_pointer_value();
                    let ptr = self
                        .codegen
                        .builder
                        .build_alloca(llvm_repr.ty, "return_value");

                    // Copy each field over into the new value.
                    // Start by allocating sufficient space on the heap for the new values.
                    repr.malloc_fields(self.codegen, self, ptr);

                    // Now, for each field, copy it over.
                    for field_name in repr.field_indices().keys() {
                        // Get the field from the source.
                        if let Some(source_field) =
                            repr.load(self.codegen, self, source, field_name)
                        {
                            // Copy the field.
                            let source_field_copied = self
                                .copy_ptr(repr.field_ty(field_name).unwrap().clone(), source_field)
                                .unwrap();
                            repr.store(self.codegen, self, ptr, source_field_copied, field_name);
                        }
                    }

                    self.codegen.builder.build_return(Some(
                        &self.codegen.builder.build_load(ptr, "return_value_deref"),
                    ));
                } else {
                    self.codegen.builder.build_return(None);
                }
            }
        }
    }

    /// Adds debug information for data types.
    pub fn create_debug_info(&mut self) {
        // Compute all the replacements from placeholder DITypes to real DIType values.
        let mut data_replacements = Vec::new();
        for repr in self.datas.values() {
            data_replacements.push(self.create_repr_debug_info(repr));
        }
        let mut enum_replacements = Vec::new();
        for repr in self.enums.values() {
            enum_replacements.push(self.create_enum_repr_debug_info(repr));
        }
        let mut asp_replacements = Vec::new();
        for repr in self.aspects.values() {
            asp_replacements.push(self.create_repr_debug_info(repr));
        }
        let mut fobj_replacements = Vec::new();
        for repr in self.func_objects.values() {
            fobj_replacements.push(self.create_repr_debug_info(repr));
        }

        // Now apply all the replacements.
        for (repr, replacement) in self.datas.values_mut().zip(data_replacements) {
            unsafe {
                self.codegen
                    .di_builder
                    .replace_placeholder_derived_type(repr.di_type, replacement);
            }
            repr.di_type = replacement;
        }
        for (repr, replacement) in self.enums.values_mut().zip(enum_replacements) {
            for (variant, replacement) in repr.variants.values_mut().zip(replacement) {
                unsafe {
                    self.codegen
                        .di_builder
                        .replace_placeholder_derived_type(variant.di_type, replacement);
                }
                variant.di_type = replacement;
            }
        }
        for (repr, replacement) in self.aspects.values_mut().zip(asp_replacements) {
            unsafe {
                self.codegen
                    .di_builder
                    .replace_placeholder_derived_type(repr.di_type, replacement);
            }
            repr.di_type = replacement;
        }
        for (repr, replacement) in self.func_objects.values_mut().zip(fobj_replacements) {
            unsafe {
                self.codegen
                    .di_builder
                    .replace_placeholder_derived_type(repr.di_type, replacement);
            }
            repr.di_type = replacement;
        }
    }

    /// Returns the new DIType associated with this repr.
    /// This is used later with `replace_placeholder_derived_type`
    /// to update all of the uses of this DIType across the program.
    fn create_repr_debug_info(&self, repr: &LLVMDataRepresentation<'ctx>) -> DIDerivedType<'ctx> {
        // Maps field indices to their DIType.
        let mut field_map = BTreeMap::new();
        for (name, idx) in repr.field_indices() {
            match idx {
                FieldIndex::Literal(i) => {
                    if let Some(repr) = repr
                        .field_types()
                        .get(name)
                        .cloned()
                        .and_then(|ty| self.repr(ty))
                    {
                        field_map.insert(*i, repr.di_type);
                    }
                }
                FieldIndex::Heap(i) => {
                    if let Some(repr) = repr
                        .field_types()
                        .get(name)
                        .cloned()
                        .and_then(|ty| self.repr(ty))
                    {
                        // TODO: how to signal that this field is behind a pointer?
                        field_map.insert(*i, repr.di_type);
                    }
                }
            }
        }

        let fields = field_map.into_iter().map(|(_i, ty)| ty).collect::<Vec<_>>();

        let di_type = self.codegen.di_builder.create_struct_type(
            repr.di_file.as_debug_info_scope(),
            &repr.name,
            repr.di_file,
            repr.range.start.line + 1,
            0,
            1,
            DIFlagsConstants::PUBLIC,
            None,
            &fields,
            0,
            None,
            &repr.name,
        );

        let di_type = self.codegen.di_builder.create_typedef(
            di_type.as_type(),
            &repr.name,
            repr.di_file,
            repr.range.start.line + 1,
            repr.di_file.as_debug_info_scope(),
            1,
        );

        di_type
    }

    fn create_enum_repr_debug_info(
        &self,
        repr: &LLVMEnumRepresentation<'ctx>,
    ) -> Vec<DIDerivedType<'ctx>> {
        repr.variants
            .values()
            .map(|variant| self.create_repr_debug_info(variant))
            .collect()
    }
}
