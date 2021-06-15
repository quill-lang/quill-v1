use std::collections::{HashMap, HashSet};

use inkwell::{
    debug_info::DIFlagsConstants,
    types::{BasicType, BasicTypeEnum},
    values::PointerValue,
    AddressSpace,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_type::{PrimitiveType, Type};

use crate::{
    codegen::CodeGenContext,
    monomorphisation::{FunctionObjectDescriptor, MonomorphisationParameters, MonomorphisedType},
};

use self::{
    any_type::AnyTypeRepresentation,
    data::{DataRepresentation, DataRepresentationBuilder, EnumRepresentation},
};

pub mod any_type;
pub mod data;
mod llvm_struct;

/// Stores the representations of all data/struct types in a project, post monomorphisation.
pub struct Representations<'a, 'ctx> {
    codegen: &'a CodeGenContext<'ctx>,
    datas: HashMap<MonomorphisedType, DataRepresentation<'ctx>>,
    enums: HashMap<MonomorphisedType, EnumRepresentation<'ctx>>,
    func_objects: HashMap<FunctionObjectDescriptor, DataRepresentation<'ctx>>,
    /// Use this type for a general function object that you don't know the type of.
    pub general_func_obj_ty: AnyTypeRepresentation<'ctx>,
}

impl<'a, 'ctx> Representations<'a, 'ctx> {
    pub fn new(
        codegen: &'a CodeGenContext<'ctx>,
        index: &ProjectIndex,
        mono_types: HashSet<MonomorphisedType>,
    ) -> Self {
        let general_func_obj_ty = codegen.context.opaque_struct_type("fobj");
        general_func_obj_ty.set_body(
            &[codegen
                .context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .into()],
            false,
        );
        let mut reprs = Self {
            codegen,
            datas: HashMap::new(),
            enums: HashMap::new(),
            func_objects: HashMap::new(),
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

        // Sort the types according to what types are used in what other types.
        // After this step, heap indirections have been added so the exact size of each type is known.
        let sorted_types = crate::sort_types::sort_types(mono_types, index);
        // println!("Sorted: {:#?}", sorted_types);

        for mono_ty in sorted_types {
            let decl = &index[&mono_ty.ty.name.source_file].types[&mono_ty.ty.name.name];
            match &decl.decl_type {
                TypeDeclarationTypeI::Data(datai) => {
                    let mut builder = DataRepresentationBuilder::new(&reprs);
                    builder.add_fields(
                        &datai.type_ctor,
                        &datai.type_params,
                        &mono_ty.ty.mono,
                        mono_ty.indirected,
                    );
                    let repr = builder.build(
                        &mono_ty.ty.name.source_file,
                        mono_ty.ty.name.range,
                        mono_ty.ty.to_string(),
                    );
                    reprs.datas.insert(mono_ty.ty, repr);
                }
                TypeDeclarationTypeI::Enum(enumi) => {
                    let repr = EnumRepresentation::new(
                        &reprs,
                        codegen,
                        enumi,
                        &mono_ty.ty,
                        mono_ty.indirected,
                    );
                    reprs.enums.insert(mono_ty.ty, repr);
                }
            };
        }

        reprs
    }

    /// If the given type needs no representation, None is returned.
    pub fn repr(&self, ty: Type) -> Option<AnyTypeRepresentation<'ctx>> {
        match ty {
            Type::Named { name, parameters } => {
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters {
                        type_parameters: parameters,
                    },
                };
                if let Some(repr) = self.datas.get(&mono_ty) {
                    repr.llvm_repr.as_ref().map(|llvm_repr| {
                        AnyTypeRepresentation::new_with_alignment(
                            BasicTypeEnum::StructType(llvm_repr.ty),
                            repr.di_type,
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
                    .create_basic_type("Bool", 1, 5, DIFlagsConstants::PUBLIC)
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
            Type::Borrow { ty, .. } => self.repr(*ty).map(|repr| {
                AnyTypeRepresentation::new(
                    self.codegen,
                    repr.llvm_type.ptr_type(AddressSpace::Generic).into(),
                    // TODO manage this pointer type
                    repr.di_type,
                )
            }),
        }
    }

    pub fn get_data(&self, descriptor: &MonomorphisedType) -> Option<&DataRepresentation<'ctx>> {
        self.datas.get(descriptor)
    }

    pub fn get_enum(&self, descriptor: &MonomorphisedType) -> Option<&EnumRepresentation<'ctx>> {
        self.enums.get(descriptor)
    }

    pub fn get_fobj(
        &self,
        descriptor: &FunctionObjectDescriptor,
    ) -> Option<&DataRepresentation<'ctx>> {
        self.func_objects.get(descriptor)
    }

    pub fn insert_fobj(
        &mut self,
        descriptor: FunctionObjectDescriptor,
        fobj: DataRepresentation<'ctx>,
    ) {
        self.func_objects.insert(descriptor, fobj);
    }

    /// Drops a value of the given type behind the given pointer.
    pub fn drop_ptr(&self, ty: Type, variable_ptr: PointerValue<'ctx>) {
        match ty.clone() {
            Type::Named { name, parameters } => {
                // We need to call this type's drop function.
                let repr = self.repr(ty);
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters {
                        type_parameters: parameters,
                    },
                };
                let func = self
                    .codegen
                    .module
                    .get_function(&format!("drop/{}", mono_ty))
                    .unwrap();
                if repr.is_some() {
                    self.codegen.builder.build_call(
                        func,
                        &[variable_ptr.into()],
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
                // TODO drop functions.
                // This will have to be done using dynamic (single) dispatch,
                // since function objects might contain things that need to be dropped/freed.
            }
            Type::Primitive(_) => {
                // No operation is required.
            }
            Type::Borrow { .. } => {
                // Dropping a borrow does nothing. No operation is required.
            }
        }
    }

    /// Create a `drop` function for each type.
    /// It is automatically populated with code that will drop each field.
    /// However, if a custom implementation of `drop` is provided, this will overwrite the default `drop` implementation.
    pub fn create_drop_funcs(&self) {
        // First, declare all the function signatures.
        for (ty, repr) in &self.datas {
            self.codegen.module.add_function(
                &format!("drop/{}", ty),
                if let Some(llvm_repr) = &repr.llvm_repr {
                    self.codegen.context.void_type().fn_type(
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
                self.codegen.context.void_type().fn_type(
                    &[repr.llvm_repr.ty.ptr_type(AddressSpace::Generic).into()],
                    false,
                ),
                None,
            );
        }

        // Now, implement the functions.
        for (ty, repr) in &self.datas {
            let func = self
                .codegen
                .module
                .get_function(&format!("drop/{}", ty))
                .unwrap();

            let block = self.codegen.context.append_basic_block(func, "drop");
            self.codegen.builder.position_at_end(block);

            if repr.llvm_repr.is_some() {
                let variable = func.get_first_param().unwrap().into_pointer_value();

                for heap_field in repr.field_names_on_heap() {
                    let ptr_to_field = repr.load(self.codegen, self, variable, heap_field).unwrap();
                    let ty = repr.field_ty(heap_field).unwrap().clone();
                    self.drop_ptr(ty, ptr_to_field);
                }

                repr.free_fields(self.codegen, variable);
            }

            self.codegen.builder.build_return(None);
        }
        for (ty, repr) in &self.enums {
            let func = self
                .codegen
                .module
                .get_function(&format!("drop/{}", ty))
                .unwrap();

            let block = self.codegen.context.append_basic_block(func, "drop");
            self.codegen.builder.position_at_end(block);

            let variable = func.get_first_param().unwrap().into_pointer_value();

            // Switch on the discriminant to see what needs dropping.
            let disc = repr.get_discriminant(self.codegen, variable);
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
                        variable,
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
    }
}
