//! Utilities for representations of data types and enum types.

use std::collections::{BTreeMap, BTreeSet};

use inkwell::{
    debug_info::{AsDIScope, DIDerivedType, DIFile, DIFlagsConstants, DIType},
    types::BasicTypeEnum,
    values::{BasicValue, PointerValue},
    AddressSpace,
};
use quill_common::location::{Range, SourceFileIdentifier};
use quill_index::{EnumI, TypeConstructorI, TypeParameter};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::CodeGenContext, debug::source_file_debug_info, sort_types::MonomorphisedItem,
};
use quill_monomorphise::{MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType};

use super::{
    any_type::AnyTypeRepresentation, llvm_struct::LLVMStructRepresentation, Representations,
};

#[derive(Debug, Clone)]
pub struct DataRepresentation<'ctx> {
    /// The LLVM representation of the data structure, if it requires a representation at all.
    pub llvm_repr: Option<LLVMStructRepresentation<'ctx>>,
    pub di_type: DIDerivedType<'ctx>,
    /// Which file defined this data type?
    pub di_file: DIFile<'ctx>,
    /// Where in the file was this type defined?
    pub range: Range,
    pub name: String,

    /// Maps Quill field names to the index of the field in the LLVM struct representation.
    /// If this contains *any* fields, `llvm_repr` is Some.
    field_indices: BTreeMap<String, FieldIndex>,
    field_types: BTreeMap<String, Type>,
}

#[derive(Debug, Copy, Clone)]
pub enum FieldIndex {
    /// The field is inside the struct at this position.
    Literal(u32),
    /// A pointer to the field is inside the struct at this position.
    Heap(u32),
}

impl<'ctx> DataRepresentation<'ctx> {
    /// Retrieves the element of this data with the given field, or None if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn load(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
        field_name: &str,
    ) -> Option<PointerValue<'ctx>> {
        self.field_indices.get(field_name).map(|field| match field {
            FieldIndex::Literal(index) => codegen
                .builder
                .build_struct_gep(ptr, *index, field_name)
                .unwrap(),
            FieldIndex::Heap(index) => {
                let ptr = codegen
                    .builder
                    .build_struct_gep(ptr, *index, field_name)
                    .unwrap();
                let ptr = codegen
                    .builder
                    .build_load(ptr, "indirect")
                    .into_pointer_value();
                // Bitcast into the correct pointer type.
                let repr = reprs
                    .repr(self.field_types.get(field_name).unwrap().clone())
                    .unwrap();
                codegen
                    .builder
                    .build_bitcast(
                        ptr,
                        match repr.llvm_type {
                            BasicTypeEnum::ArrayType(ty) => ty.ptr_type(AddressSpace::Generic),
                            BasicTypeEnum::FloatType(ty) => ty.ptr_type(AddressSpace::Generic),
                            BasicTypeEnum::IntType(ty) => ty.ptr_type(AddressSpace::Generic),
                            BasicTypeEnum::PointerType(ty) => ty.ptr_type(AddressSpace::Generic),
                            BasicTypeEnum::StructType(ty) => ty.ptr_type(AddressSpace::Generic),
                            BasicTypeEnum::VectorType(ty) => ty.ptr_type(AddressSpace::Generic),
                        },
                        "indirect_bitcast",
                    )
                    .into_pointer_value()
            }
        })
    }

    /// Stores a value into the element of this data with the given field, or panics no operation if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn store<V: BasicValue<'ctx>>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
        value: V,
        field_name: &str,
    ) {
        let dest = self.load(codegen, reprs, ptr, field_name).unwrap();
        codegen.builder.build_store(dest, {
            // If the value was a function object, first cast it to a generic `fobj`.
            if matches!(self.field_types.get(field_name), Some(Type::Function(_, _))) {
                codegen
                    .builder
                    .build_bitcast(value, reprs.general_func_obj_ty.llvm_type, "fobj_bitcast")
                    .as_basic_value_enum()
            } else {
                value.as_basic_value_enum()
            }
        });
    }

    /// Stores the value behind the given pointer inside this struct.
    pub fn store_ptr(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
        src: PointerValue<'ctx>,
        field_name: &str,
    ) {
        self.store(
            codegen,
            reprs,
            ptr,
            codegen.builder.build_load(src, "value_to_store"),
            field_name,
        )
    }

    /// Lists the fields which are stored indirectly (on the heap).
    pub fn field_names_on_heap(&self) -> Vec<&str> {
        self.field_indices
            .iter()
            .filter_map(|(k, v)| {
                if matches!(v, FieldIndex::Heap(_)) {
                    Some(k.as_str())
                } else {
                    None
                }
            })
            .collect()
    }

    /// Checks to see if a field *with representation* exists in this data structure.
    pub fn has_field(&self, name: &str) -> bool {
        self.field_indices.contains_key(name)
    }

    /// Retrieves the type of the given field.
    pub fn field_ty(&self, name: &str) -> Option<&Type> {
        self.field_types.get(name)
    }

    /// Allocate space for indirect fields of this struct.
    pub fn malloc_fields(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
    ) {
        for (field_name, index) in &self.field_indices {
            if let FieldIndex::Heap(index) = index {
                // Malloc this field.
                let ty = reprs.repr(self.field_types[field_name].clone()).unwrap();
                let llvm_type_ptr = match ty.llvm_type {
                    BasicTypeEnum::ArrayType(ty) => ty.ptr_type(AddressSpace::Generic),
                    BasicTypeEnum::FloatType(ty) => ty.ptr_type(AddressSpace::Generic),
                    BasicTypeEnum::IntType(ty) => ty.ptr_type(AddressSpace::Generic),
                    BasicTypeEnum::PointerType(ty) => ty.ptr_type(AddressSpace::Generic),
                    BasicTypeEnum::StructType(ty) => ty.ptr_type(AddressSpace::Generic),
                    BasicTypeEnum::VectorType(ty) => ty.ptr_type(AddressSpace::Generic),
                };
                let malloc = codegen
                    .builder
                    .build_call(
                        codegen.libc("malloc"),
                        &[codegen
                            .context
                            .i64_type()
                            .const_int(codegen.target_data().get_store_size(&ty.llvm_type), false)
                            .into()],
                        "malloc_invocation",
                    )
                    .try_as_basic_value()
                    .unwrap_left();
                let malloc = codegen.builder.build_bitcast(
                    malloc,
                    llvm_type_ptr,
                    "malloc_invocation_bitcast",
                );
                let field = codegen
                    .builder
                    .build_struct_gep(ptr, *index, field_name)
                    .unwrap();
                let field_bitcast = codegen
                    .builder
                    .build_bitcast(
                        field,
                        llvm_type_ptr.ptr_type(AddressSpace::Generic),
                        field_name,
                    )
                    .into_pointer_value();
                codegen.builder.build_store(field_bitcast, malloc);
            }
        }
    }

    /// Deallocate space for indirect fields of this struct.
    pub fn free_fields(&self, codegen: &CodeGenContext<'ctx>, ptr: PointerValue<'ctx>) {
        for (field_name, index) in &self.field_indices {
            if let FieldIndex::Heap(index) = index {
                // Free this field.
                let field = codegen
                    .builder
                    .build_struct_gep(ptr, *index, field_name)
                    .unwrap();
                let field_value = codegen.builder.build_load(field, "field_loaded");
                codegen
                    .builder
                    .build_call(
                        codegen.module.get_function("free").unwrap(),
                        &[field_value],
                        "free_invocation",
                    )
                    .try_as_basic_value()
                    .unwrap_right();
            }
        }
    }

    /// Get a reference to the data representation's field indices.
    pub fn field_indices(&self) -> &BTreeMap<String, FieldIndex> {
        &self.field_indices
    }

    /// Get a reference to the data representation's field types.
    pub fn field_types(&self) -> &BTreeMap<String, Type> {
        &self.field_types
    }
}

#[derive(Debug)]
pub struct EnumRepresentation<'ctx> {
    /// The LLVM representation of the enum structure.
    /// Enums always have a representation, since they always have a discriminant to store.
    pub llvm_repr: LLVMStructRepresentation<'ctx>,
    pub di_type: DIType<'ctx>,
    /// Maps variant names to data representations of the enum variants.
    /// If a discriminant is required in the data representation, it will have field name `.discriminant`.
    pub variants: BTreeMap<String, DataRepresentation<'ctx>>,
    /// The discriminant values associated with each variant, if there is a discriminant.
    pub variant_discriminants: BTreeMap<String, u64>,
}

impl<'ctx> EnumRepresentation<'ctx> {
    /// By this point, `reprs` should contain the representations of all (non-indirected) fields in this enum type.
    pub fn new<'a>(
        reprs: &Representations<'a, 'ctx>,
        codegen: &CodeGenContext<'ctx>,
        ty: &EnumI,
        mono: &MonomorphisedType,
        indirected_types: Vec<MonomorphisedItem>,
    ) -> Self {
        // Construct each enum variant as a data type with an extra integer discriminant field at the start.
        let variants = ty
            .variants
            .iter()
            .map(|variant| {
                let mut builder = DataRepresentationBuilder::new(reprs);
                builder.add_field(
                    ".discriminant".to_string(),
                    Type::Primitive(PrimitiveType::Int),
                    &ty.type_params,
                    &mono.mono,
                    false,
                );
                builder.add_fields(
                    &variant.type_ctor,
                    &ty.type_params,
                    &mono.mono,
                    indirected_types.clone(),
                );

                (
                    variant.name.name.clone(),
                    builder.build(
                        &mono.name.source_file,
                        ty.range,
                        format!("{}@{}", mono, variant.name.name),
                    ),
                )
            })
            .collect::<BTreeMap<_, _>>();

        // Now work out the largest size of an enum variant and use that as the size of the "base" enum case.
        let size = variants
            .values()
            .map(|repr| {
                codegen
                    .target_data()
                    .get_store_size(&repr.llvm_repr.as_ref().unwrap().ty)
            })
            .max()
            .unwrap();
        let alignment = variants
            .values()
            .map(|repr| {
                codegen
                    .target_data()
                    .get_abi_alignment(&repr.llvm_repr.as_ref().unwrap().ty)
            })
            .max()
            .unwrap();

        // Add padding to ensure that the alignment of the enum variant inside the enum matches the alignment of the enum itself.
        let discriminant_size = codegen
            .target_data()
            .get_store_size(&codegen.context.i64_type());
        let padding_size = alignment.saturating_sub(discriminant_size as u32);

        let llvm_field_types = vec![
            BasicTypeEnum::IntType(codegen.context.i64_type()),
            BasicTypeEnum::ArrayType(codegen.context.i8_type().array_type(padding_size)),
            BasicTypeEnum::ArrayType(
                codegen
                    .context
                    .i8_type()
                    .array_type(size as u32 - padding_size - discriminant_size as u32),
            ),
        ];
        let llvm_ty = codegen.context.opaque_struct_type(&mono.to_string());
        llvm_ty.set_body(&llvm_field_types, false);

        let variant_discriminants = ty
            .variants
            .iter()
            .enumerate()
            .map(|(i, variant)| (variant.name.name.clone(), i as u64))
            .collect::<BTreeMap<_, _>>();

        let file = source_file_debug_info(codegen, &mono.name.source_file);
        let di_type = codegen.di_builder.create_struct_type(
            file.as_debug_info_scope(),
            "<function object>",
            file,
            ty.range.start.line + 1,
            0,
            1,
            DIFlagsConstants::PUBLIC,
            None,
            &[],
            0,
            None,
            &mono.to_string(),
        );

        EnumRepresentation {
            llvm_repr: LLVMStructRepresentation::new_with_alignment(llvm_ty, alignment),
            di_type: di_type.as_type(),
            variants,
            variant_discriminants,
        }
    }

    /// Retrieves the element of this data with the given field, or None if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn load(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
        variant: &str,
        field: &str,
    ) -> Option<PointerValue<'ctx>> {
        // println!("Loading {} from {}", field, variant);
        self.variants.get(variant).and_then(|variant| {
            // Bitcast the pointer to a pointer to the correct enum variant.
            let ptr_bitcast = codegen
                .builder
                .build_bitcast(
                    ptr,
                    variant
                        .llvm_repr
                        .as_ref()
                        .unwrap()
                        .ty
                        .ptr_type(AddressSpace::Generic),
                    "variant_bitcast",
                )
                .into_pointer_value();
            variant.load(codegen, reprs, ptr_bitcast, field)
        })
    }

    /// Gets the discriminant of this enum.
    pub fn get_discriminant(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
    ) -> PointerValue<'ctx> {
        codegen
            .builder
            .build_struct_gep(ptr, 0, "discriminant_ptr")
            .unwrap()
    }

    /// Assigns the discriminant of this enum to represent the given variant.
    pub fn store_discriminant(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &Representations<'_, 'ctx>,
        ptr: PointerValue<'ctx>,
        variant: &str,
    ) {
        if let Some(discriminant) = self.variant_discriminants.get(variant) {
            self.variants[variant].store(
                codegen,
                reprs,
                ptr,
                codegen.context.i64_type().const_int(*discriminant, false),
                ".discriminant",
            );
        }
    }
}

pub struct DataRepresentationBuilder<'a, 'ctx> {
    reprs: &'a Representations<'a, 'ctx>,

    llvm_field_types: Vec<BasicTypeEnum<'ctx>>,
    field_indices: BTreeMap<String, FieldIndex>,
    field_types: BTreeMap<String, Type>,

    /// If a field's name is in this set, it can be accessed only behind a heap pointer.
    indirect_fields: BTreeSet<String>,
}

impl<'a, 'ctx> DataRepresentationBuilder<'a, 'ctx> {
    pub fn new(reprs: &'a Representations<'a, 'ctx>) -> Self {
        Self {
            reprs,
            llvm_field_types: Vec::new(),
            field_indices: BTreeMap::new(),
            field_types: BTreeMap::new(),
            indirect_fields: BTreeSet::new(),
        }
    }

    pub fn add_field(
        &mut self,
        field_name: String,
        field_type: Type,
        type_params: &[TypeParameter],
        mono: &MonomorphisationParameters,
        indirect: bool,
    ) {
        self.field_types
            .insert(field_name.clone(), field_type.clone());
        if indirect {
            self.indirect_fields.insert(field_name.clone());
            self.add_field_raw(field_name, None);
        } else if let Some(repr) = self.reprs.repr(replace_type_variables(
            field_type,
            type_params,
            mono.type_parameters(),
        )) {
            self.add_field_raw(field_name, Some(repr));
        } else {
            // This field had no representation.
        }
    }

    /// Does not cache a MIR type, only stores the LLVM type.
    /// If `repr` is None, this field is considered to be an "indirect" field, and a i8* is stored instead of the type itself.
    pub fn add_field_raw(&mut self, field_name: String, repr: Option<AnyTypeRepresentation<'ctx>>) {
        if let Some(repr) = repr {
            self.field_indices.insert(
                field_name,
                FieldIndex::Literal(self.llvm_field_types.len() as u32),
            );
            self.llvm_field_types.push(repr.llvm_type);
        } else {
            self.field_indices.insert(
                field_name,
                FieldIndex::Heap(self.llvm_field_types.len() as u32),
            );
            self.llvm_field_types.push(
                self.reprs
                    .codegen
                    .context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .into(),
            );
        }
    }

    /// Like `add_field_raw` but you can specify the Quill type associated with this field.
    pub fn add_field_raw_with_type(
        &mut self,
        field_name: String,
        repr: Option<AnyTypeRepresentation<'ctx>>,
        ty: Type,
    ) {
        self.field_types.insert(field_name.clone(), ty);
        self.add_field_raw(field_name, repr);
    }

    /// Add the fields from a type constructor to this data type.
    pub fn add_fields(
        &mut self,
        type_ctor: &TypeConstructorI,
        type_params: &[TypeParameter],
        mono: &MonomorphisationParameters,
        indirected_types: Vec<MonomorphisedItem>,
    ) {
        for (field_name, field_ty) in &type_ctor.fields {
            let field_ty =
                replace_type_variables(field_ty.clone(), type_params, mono.type_parameters());
            let indirect = match &field_ty {
                Type::Named { name, parameters } => {
                    indirected_types.contains(&MonomorphisedItem::Type(MonomorphisedType {
                        name: name.clone(),
                        mono: MonomorphisationParameters::new(parameters.clone()),
                    }))
                }
                Type::Impl { name, parameters } => {
                    indirected_types.contains(&MonomorphisedItem::Aspect(MonomorphisedAspect {
                        name: name.clone(),
                        mono: MonomorphisationParameters::new(parameters.clone()),
                    }))
                }
                _ => false,
            };

            self.add_field(
                field_name.name.clone(),
                field_ty,
                type_params,
                mono,
                indirect,
            );
        }
    }

    /// Returns a data representation.
    pub fn build(
        self,
        file: &SourceFileIdentifier,
        range: Range,
        name: String,
    ) -> DataRepresentation<'ctx> {
        let di_file = source_file_debug_info(self.reprs.codegen, file);

        let di_type = unsafe {
            self.reprs
                .codegen
                .di_builder
                .create_placeholder_derived_type(self.reprs.codegen.context)
        };

        if self.llvm_field_types.is_empty() {
            DataRepresentation {
                llvm_repr: None,
                di_type,
                di_file,
                range,
                field_indices: self.field_indices,
                field_types: self.field_types,
                name,
            }
        } else {
            let llvm_ty = self.reprs.codegen.context.opaque_struct_type(&name);
            llvm_ty.set_body(&self.llvm_field_types, false);
            DataRepresentation {
                llvm_repr: Some(LLVMStructRepresentation::new(self.reprs.codegen, llvm_ty)),
                di_type,
                di_file,
                range,
                field_indices: self.field_indices,
                field_types: self.field_types,
                name,
            }
        }
    }
}
