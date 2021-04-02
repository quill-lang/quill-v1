//! Computes the LLVM data representation of a data or enum declaration in Quill code,
//! and generates indices for GEP calls in LLVM IR.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
    unimplemented,
};

use inkwell::{
    types::{BasicTypeEnum, FunctionType, StructType},
    values::{BasicValue, PointerValue},
    AddressSpace,
};
use quill_common::name::QualifiedName;
use quill_index::{EnumI, ProjectIndex, TypeConstructorI, TypeDeclarationTypeI, TypeParameter};
use quill_mir::{ArgumentIndex, DefinitionBodyM, LocalVariableName, ProjectMIR, StatementKind};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::codegen::CodeGenContext;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisationParameters {
    pub type_parameters: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisedType {
    pub name: QualifiedName,
    pub mono: MonomorphisationParameters,
}

impl Display for MonomorphisedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t/{}", self.name)?;
        if !self.mono.type_parameters.is_empty() {
            write!(f, "[")?;
            for ty_param in &self.mono.type_parameters {
                write!(f, "{},", ty_param)?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

/// A monomorphised type, where some of its fields may have a layer of heap indirection.
#[derive(Debug)]
struct IndirectedMonomorphisedType {
    ty: MonomorphisedType,
    /// The list of fields that require a level of heap indirection.
    /// If `ty` is an enum type, the first element of this tuple is the variant that the field belongs to.
    indirected: Vec<(Option<String>, String)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisedFunction {
    pub func: QualifiedName,
    pub mono: MonomorphisationParameters,
    /// Must never contain a zero.
    pub curry_steps: Vec<u64>,
    /// If this is true, the function will be monomorphised as a "direct" function; no function pointer is supplied and
    /// all arguments before (but NOT including) the given curry steps are given as function parameters. The return type is a function object
    /// that will compute the result of the function when executed with an "indirect" function call (or multiple in a chain).
    /// If this is false, the function is considered "indirect"; a function pointer (representing this function) is supplied as
    /// the first parameter. The next n parameters are the params for the first curry step.
    ///
    /// For example, if `curry_steps = [1,1]`, `arity = 2`, and `direct = false` then the function's signature will be
    /// `(fobj0, first parameter) -> fobj1` where `fobj0` is a function object containing no data, and `fobj1` is a function
    /// object storing the first parameter, pointing to an this function with `curry_steps = [1]` and `direct = false`.
    ///
    /// If `curry_steps = [1,1]`, `arity = 2`, and `direct = true` then the function's signature will be
    /// `() -> fobj0` where `fobj0` if a function object containing no data and pointing to this function with `curry_steps = [1,1]`
    /// and `direct = false`.
    ///
    /// We can think of indirect functions as "going one level down the currying chain", since they always consume and emit a function
    /// object (unless, of course, this is the last currying step - in which case the actual function is executed and its return type
    /// becomes the only return value). Direct functions allow us to "jump inside the currying chain" - providing an amount of parameters,
    /// we can create a function object holding these parameters.
    pub direct: bool,
}

impl Display for MonomorphisedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.func)?;
        if !self.mono.type_parameters.is_empty() {
            write!(f, "[")?;
            for ty_param in &self.mono.type_parameters {
                write!(f, "{},", ty_param)?;
            }
            write!(f, "]")?;
        }
        write!(f, "{:?}", self.curry_steps)?;
        if self.direct {
            write!(f, "d")
        } else {
            write!(f, "i")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionObjectDescriptor {
    pub func: QualifiedName,
    pub mono: MonomorphisationParameters,
    /// If this monomorphisation of this function requires a currying step,
    /// this contains the amount of parameters applied in the *last* such step.
    pub last_curry_step: Option<u64>,
}

impl Display for FunctionObjectDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "o/{}", self.func)?;
        if !self.mono.type_parameters.is_empty() {
            write!(f, "[")?;
            for ty_param in &self.mono.type_parameters {
                write!(f, "{},", ty_param)?;
            }
            write!(f, "]")?;
        }
        if let Some(last) = self.last_curry_step {
            write!(f, "{}", last)?;
        }
        Ok(())
    }
}

/// Stores the representations of a monomorphised function's arguments and return type.
struct ArgReprs<'ctx> {
    /// For each argument of the original Quill function, what argument index in LLVM was it mapped to?
    /// If it had no representation, this returns None.
    arg_repr_indices: Vec<Option<usize>>,
    args_with_reprs: Vec<AnyTypeRepresentation<'ctx>>,
    return_type: Option<BasicTypeEnum<'ctx>>,
    arity: u64,
    function_object: DataRepresentation<'ctx>,
}

impl MonomorphisedFunction {
    pub fn function_object_descriptor(&self) -> FunctionObjectDescriptor {
        FunctionObjectDescriptor {
            func: self.func.clone(),
            mono: self.mono.clone(),
            last_curry_step: self.curry_steps.last().copied(),
        }
    }

    fn generate_arg_reprs<'ctx>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &mut Representations<'_, 'ctx>,
        mir: &ProjectMIR,
    ) -> ArgReprs<'ctx> {
        let def = &mir.files[&self.func.source_file].definitions[&self.func.name];

        let args_options = (0..def.arity)
            .map(|i| {
                let info = def
                    .local_variable_names
                    .get(&LocalVariableName::Argument(ArgumentIndex(i)))
                    .unwrap();
                let ty = replace_type_variables(
                    info.ty.clone(),
                    &def.type_variables,
                    &self.mono.type_parameters,
                );
                reprs.repr(ty)
            })
            .collect::<Vec<_>>();

        let mut arg_repr_indices = Vec::new();
        for arg in &args_options {
            arg_repr_indices.push(arg.map(|_| arg_repr_indices.len()));
        }
        let args_with_reprs = args_options.iter().copied().flatten().collect::<Vec<_>>();

        let return_type = replace_type_variables(
            def.return_type.clone(),
            &def.type_variables,
            &self.mono.type_parameters,
        );

        let descriptor = self.function_object_descriptor();
        let function_object = if let Some(repr) = reprs.func_objects.get(&descriptor) {
            repr.clone()
        } else {
            let mut builder = DataRepresentationBuilder::new(reprs);
            // Add the function pointer as the first field.
            builder.add_field_raw(
                ".fptr".to_string(),
                AnyTypeRepresentation {
                    llvm_type: codegen
                        .context
                        .i8_type()
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                    size: 8,
                    alignment: 8,
                },
            );
            // Add only the arguments not pertaining to the last currying step.
            for i in 0..def.arity - self.curry_steps.last().copied().unwrap_or(0) {
                if let Some(repr) = arg_repr_indices[i as usize].map(|i| args_with_reprs[i]) {
                    builder.add_field_raw(format!("field_{}", i), repr);
                }
            }

            let repr = builder.build(descriptor.to_string());
            reprs.func_objects.insert(descriptor, repr.clone());
            repr
        };

        ArgReprs {
            arg_repr_indices,
            args_with_reprs,
            return_type: reprs.repr(return_type).map(|repr| repr.llvm_type),
            arity: def.arity,
            function_object,
        }
    }

    fn generate_llvm_type<'ctx>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &mut Representations<'_, 'ctx>,
        mir: &ProjectMIR,
    ) -> FunctionType<'ctx> {
        let arg_reprs = self.generate_arg_reprs(codegen, reprs, mir);

        let curry_steps_amount = self.curry_steps.iter().sum::<u64>() as usize;

        // Check to see if this function is direct or indirect.
        if self.direct {
            // The parameters to this function are exactly the first n arguments, where n = arity - sum(curry_steps).
            // But some of these args may not have representations, so we'll need to be careful.
            let real_args = (0..arg_reprs.arity as usize
                - self.curry_steps.iter().sum::<u64>() as usize)
                .filter_map(|idx| {
                    arg_reprs.arg_repr_indices[idx]
                        .map(|idx| arg_reprs.args_with_reprs[idx].llvm_type)
                })
                .collect::<Vec<_>>();

            // The return value is the function return type if curry_steps_amount == 0, else it's a function object.
            if curry_steps_amount == 0 {
                arg_reprs
                    .return_type
                    .map(|repr| match repr {
                        BasicTypeEnum::ArrayType(array) => array.fn_type(&real_args, false),
                        BasicTypeEnum::FloatType(float) => float.fn_type(&real_args, false),
                        BasicTypeEnum::IntType(int) => int.fn_type(&real_args, false),
                        BasicTypeEnum::PointerType(ptr) => ptr.fn_type(&real_args, false),
                        BasicTypeEnum::StructType(a_struct) => a_struct.fn_type(&real_args, false),
                        BasicTypeEnum::VectorType(vec) => vec.fn_type(&real_args, false),
                    })
                    .unwrap_or_else(|| codegen.context.void_type().fn_type(&real_args, false))
            } else {
                arg_reprs
                    .function_object
                    .llvm_repr
                    .unwrap()
                    .ty
                    .ptr_type(AddressSpace::Generic)
                    .fn_type(&real_args, false)
            }
        } else {
            // The parameters to this function are a function ptr, and then the first n arguments, where n = curry_steps[0].
            // But some of these args may not have representations, so we'll need to be careful.
            let mut real_args = vec![arg_reprs
                .function_object
                .llvm_repr
                .as_ref()
                .unwrap()
                .ty
                .ptr_type(AddressSpace::Generic)
                .into()];
            let args_already_calculated = arg_reprs.arity as usize - curry_steps_amount;
            real_args.extend(
                (args_already_calculated..args_already_calculated + self.curry_steps[0] as usize)
                    .filter_map(|idx| {
                        arg_reprs.arg_repr_indices[idx]
                            .map(|idx| arg_reprs.args_with_reprs[idx].llvm_type)
                    }),
            );

            if self.curry_steps.len() == 1 {
                arg_reprs
                    .return_type
                    .map(|repr| match repr {
                        BasicTypeEnum::ArrayType(array) => array.fn_type(&real_args, false),
                        BasicTypeEnum::FloatType(float) => float.fn_type(&real_args, false),
                        BasicTypeEnum::IntType(int) => int.fn_type(&real_args, false),
                        BasicTypeEnum::PointerType(ptr) => ptr.fn_type(&real_args, false),
                        BasicTypeEnum::StructType(a_struct) => a_struct.fn_type(&real_args, false),
                        BasicTypeEnum::VectorType(vec) => vec.fn_type(&real_args, false),
                    })
                    .unwrap_or_else(|| codegen.context.void_type().fn_type(&real_args, false))
            } else {
                arg_reprs
                    .function_object
                    .llvm_repr
                    .unwrap()
                    .ty
                    .ptr_type(AddressSpace::Generic)
                    .fn_type(&real_args, false)
            }
        }
    }

    /// Generates the LLVM type representing this function, then adds the type to the codegen module.
    pub fn add_llvm_type<'ctx>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        reprs: &mut Representations<'_, 'ctx>,
        mir: &ProjectMIR,
    ) {
        let ty = self.generate_llvm_type(codegen, reprs, mir);
        codegen.module.add_function(&self.to_string(), ty, None);
    }
}

#[derive(Copy, Clone)]
pub enum FieldIndex {
    /// The field is inside the struct at this position.
    Literal(u32),
    /// A pointer to the field is inside the struct at this position.
    Heap(u32),
}

#[derive(Clone)]
pub struct LLVMRepresentation<'ctx> {
    pub ty: StructType<'ctx>,
    pub size: u32,
    pub alignment: u32,
}

#[derive(Clone)]
pub struct DataRepresentation<'ctx> {
    /// The LLVM representation of the data structure, if it requires a representation at all.
    pub llvm_repr: Option<LLVMRepresentation<'ctx>>,
    /// Maps Quill field names to the index of the field in the LLVM struct representation.
    /// If this contains *any* fields, `llvm_repr` is Some.
    field_indices: HashMap<String, FieldIndex>,
    field_types: HashMap<String, Type>,
    field_sizes: HashMap<String, u64>,
    field_alignments: HashMap<String, u64>,
    name: String,
}

impl<'ctx> DataRepresentation<'ctx> {
    /// Retrieves the element of this data with the given field, or None if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn load(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
        field: &str,
    ) -> Option<PointerValue<'ctx>> {
        self.field_indices.get(field).map(|field| match field {
            FieldIndex::Literal(index) => codegen
                .builder
                .build_struct_gep(ptr, *index, &self.name)
                .unwrap(),
            FieldIndex::Heap(_) => unimplemented!(),
        })
    }

    /// Stores a value into the element of this data with the given field, or panics no operation if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn store<V: BasicValue<'ctx>>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
        value: V,
        field_name: &str,
    ) {
        let field = self.field_indices.get(field_name).unwrap();
        match field {
            FieldIndex::Literal(index) => {
                let ptr = codegen
                    .builder
                    .build_struct_gep(ptr, *index, field_name)
                    .unwrap();
                codegen.builder.build_store(ptr, value);
            }
            FieldIndex::Heap(_) => unimplemented!(),
        }
    }

    /// Stores the value behind the given pointer inside this struct.
    pub fn store_ptr(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
        src: PointerValue<'ctx>,
        field_name: &str,
    ) {
        let dest = self.load(codegen, ptr, field_name).unwrap();
        codegen
            .builder
            .build_memcpy(
                dest,
                self.field_alignments[field_name] as u32,
                src,
                self.field_alignments[field_name] as u32,
                codegen
                    .context
                    .ptr_sized_int_type(codegen.target_data(), None)
                    .const_int(self.field_sizes[field_name], false),
            )
            .unwrap();
    }

    /// Checks to see if a field *with representation* exists in this data structure.
    pub fn has_field(&self, name: &str) -> bool {
        self.field_indices.contains_key(name)
    }

    pub fn field_ty(&self, name: &str) -> &Type {
        &self.field_types[name]
    }
}

pub struct EnumRepresentation<'ctx> {
    /// The LLVM representation of the enum structure.
    pub llvm_repr: LLVMRepresentation<'ctx>,
    /// Maps variant names to data representations of the enum variants.
    /// If a discriminant is required in the data representation, it will have field name `.discriminant`.
    pub variants: HashMap<String, DataRepresentation<'ctx>>,
    /// The discriminant values associated with each variant, if there is a discriminant.
    pub variant_discriminants: HashMap<String, u64>,
}

impl<'ctx> EnumRepresentation<'ctx> {
    /// Retrieves the element of this data with the given field, or None if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn load(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
        variant: &str,
        field: &str,
    ) -> Option<PointerValue<'ctx>> {
        self.variants
            .get(variant)
            .and_then(|variant| variant.load(codegen, ptr, field))
    }

    /// Stores a value into the element of this data with the given field, or panics no operation if no such field exists,
    /// or if there was no representation for the field.
    /// `ptr` is a pointer to this struct.
    /// This uses the codegen builder to append instructions if required.
    pub fn store<V: BasicValue<'ctx>>(
        &self,
        codegen: &CodeGenContext<'ctx>,
        ptr: PointerValue<'ctx>,
        value: V,
        variant: &str,
        field_name: &str,
    ) {
        self.variants
            .get(variant)
            .unwrap()
            .store(codegen, ptr, value, field_name);
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
        ptr: PointerValue<'ctx>,
        variant: &str,
    ) {
        if let Some(discriminant) = self.variant_discriminants.get(variant) {
            self.variants[variant].store(
                codegen,
                ptr,
                codegen.context.i64_type().const_int(*discriminant, false),
                ".discriminant",
            );
        }
    }
}

struct DataRepresentationBuilder<'a, 'ctx> {
    reprs: &'a Representations<'a, 'ctx>,

    llvm_field_types: Vec<BasicTypeEnum<'ctx>>,
    field_indices: HashMap<String, FieldIndex>,
    field_types: HashMap<String, Type>,
    field_sizes: HashMap<String, u64>,
    field_alignments: HashMap<String, u64>,

    size: u32,
    alignment: u32,
}

impl<'a, 'ctx> DataRepresentationBuilder<'a, 'ctx> {
    fn new(reprs: &'a Representations<'a, 'ctx>) -> Self {
        Self {
            reprs,
            llvm_field_types: Vec::new(),
            field_indices: HashMap::new(),
            field_types: HashMap::new(),
            field_sizes: HashMap::new(),
            field_alignments: HashMap::new(),
            size: 0,
            alignment: 1,
        }
    }

    fn add_field(
        &mut self,
        field_name: String,
        field_type: Type,
        type_params: &[TypeParameter],
        mono: &MonomorphisationParameters,
    ) {
        self.field_types
            .insert(field_name.clone(), field_type.clone());
        if let Some(repr) = self.reprs.repr(replace_type_variables(
            field_type,
            &type_params,
            &mono.type_parameters,
        )) {
            self.add_field_raw(field_name, repr);
        } else {
            // This field had no representation.
        }
    }

    /// Does not cache a MIR type, only stores the LLVM type.
    fn add_field_raw(&mut self, field_name: String, repr: AnyTypeRepresentation<'ctx>) {
        self.field_sizes
            .insert(field_name.clone(), repr.size as u64);
        self.field_alignments
            .insert(field_name.clone(), repr.alignment as u64);
        self.field_indices.insert(
            field_name,
            FieldIndex::Literal(self.llvm_field_types.len() as u32),
        );
        self.llvm_field_types.push(repr.llvm_type);

        // Update size and alignment.
        self.alignment = std::cmp::max(self.alignment, repr.alignment);
        // Increase the size of the object (essentially adding padding) until it's a multiple of `repr.alignment`.
        let padding_to_add = repr.alignment - self.size % repr.alignment;
        self.size += if padding_to_add == repr.alignment {
            0
        } else {
            padding_to_add
        };
        self.size += repr.size;
    }

    /// Add the fields from a type constructor to this data type.
    fn add_fields(
        &mut self,
        type_ctor: &TypeConstructorI,
        type_params: &[TypeParameter],
        mono: &MonomorphisationParameters,
        indirected_fields: Vec<String>,
    ) {
        for (field_name, field_ty) in &type_ctor.fields {
            self.add_field(field_name.name.clone(), field_ty.clone(), type_params, mono);
        }
    }

    /// Returns a data representation.
    fn build(self, name: String) -> DataRepresentation<'ctx> {
        if self.llvm_field_types.is_empty() {
            DataRepresentation {
                llvm_repr: None,
                field_indices: self.field_indices,
                field_types: self.field_types,
                field_sizes: self.field_sizes,
                field_alignments: self.field_alignments,
                name,
            }
        } else {
            let llvm_ty = self.reprs.codegen.context.opaque_struct_type(&name);
            llvm_ty.set_body(&self.llvm_field_types, false);
            DataRepresentation {
                llvm_repr: Some(LLVMRepresentation {
                    ty: llvm_ty,
                    size: self.size,
                    alignment: self.alignment,
                }),
                field_indices: self.field_indices,
                field_types: self.field_types,
                field_sizes: self.field_sizes,
                field_alignments: self.field_alignments,
                name,
            }
        }
    }
}

impl<'a, 'ctx> EnumRepresentation<'ctx> {
    /// By this point, `reprs` should contain the representations of all (non-indirected) fields in this enum type.
    fn new(
        reprs: &Representations<'a, 'ctx>,
        codegen: &CodeGenContext<'ctx>,
        ty: &EnumI,
        mono: &MonomorphisedType,
        indirected_fields: Vec<(String, String)>,
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
                );
                builder.add_fields(
                    &variant.type_ctor,
                    &ty.type_params,
                    &mono.mono,
                    indirected_fields
                        .iter()
                        .filter_map(|(variant_name, field_name)| {
                            if *variant_name == variant.name.name {
                                Some(field_name.clone())
                            } else {
                                None
                            }
                        })
                        .collect(),
                );

                (
                    variant.name.name.clone(),
                    builder.build(format!("{}@{}", mono, variant.name.name)),
                )
            })
            .collect::<HashMap<_, _>>();

        // Now work out the largest size of an enum variant and use that as the size of the "base" enum case.
        let size = variants
            .values()
            .map(|repr| repr.llvm_repr.as_ref().unwrap().size)
            .max()
            .unwrap();
        let alignment = variants
            .values()
            .map(|repr| repr.llvm_repr.as_ref().unwrap().alignment)
            .max()
            .unwrap();

        let llvm_field_types = vec![
            BasicTypeEnum::IntType(codegen.context.i64_type()),
            BasicTypeEnum::ArrayType(codegen.context.i8_type().array_type(size - 8)),
        ];
        let llvm_ty = codegen.context.opaque_struct_type(&mono.to_string());
        llvm_ty.set_body(&llvm_field_types, false);

        let variant_discriminants = ty
            .variants
            .iter()
            .enumerate()
            .map(|(i, variant)| (variant.name.name.clone(), i as u64))
            .collect::<HashMap<_, _>>();

        EnumRepresentation {
            llvm_repr: LLVMRepresentation {
                ty: llvm_ty,
                size,
                alignment,
            },
            variants,
            variant_discriminants,
        }
    }
}

/// Stores the representations of all data/struct types in a project, post monomorphisation.
pub struct Representations<'a, 'ctx> {
    codegen: &'a CodeGenContext<'ctx>,
    datas: HashMap<MonomorphisedType, DataRepresentation<'ctx>>,
    enums: HashMap<MonomorphisedType, EnumRepresentation<'ctx>>,
    func_objects: HashMap<FunctionObjectDescriptor, DataRepresentation<'ctx>>,
    /// Use this type for a general function object that you don't know the type of.
    pub general_func_obj_ty: AnyTypeRepresentation<'ctx>,
}

#[derive(Debug, Clone, Copy)]
pub struct AnyTypeRepresentation<'ctx> {
    pub llvm_type: BasicTypeEnum<'ctx>,
    pub size: u32,
    pub alignment: u32,
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
            general_func_obj_ty: AnyTypeRepresentation {
                llvm_type: general_func_obj_ty.ptr_type(AddressSpace::Generic).into(),
                size: 8,
                alignment: 8,
            },
        };

        // Sort the types according to what types are used in what other types.
        // After this step, heap indirections have been added so the exact size of each type is known.
        let sorted_types = sort_types(mono_types, index);
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
                        mono_ty
                            .indirected
                            .into_iter()
                            .map(|(opt, field)| {
                                assert!(opt.is_none());
                                field
                            })
                            .collect(),
                    );
                    let repr = builder.build(mono_ty.ty.to_string());
                    reprs.datas.insert(mono_ty.ty, repr);
                }
                TypeDeclarationTypeI::Enum(enumi) => {
                    let repr = EnumRepresentation::new(
                        &reprs,
                        codegen,
                        enumi,
                        &mono_ty.ty,
                        mono_ty
                            .indirected
                            .into_iter()
                            .map(|(opt, field)| (opt.unwrap(), field))
                            .collect(),
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
                    repr.llvm_repr.as_ref().map(|repr| AnyTypeRepresentation {
                        llvm_type: BasicTypeEnum::StructType(repr.ty),
                        size: repr.size,
                        alignment: repr.alignment,
                    })
                } else if let Some(repr) = self.enums.get(&mono_ty) {
                    Some(AnyTypeRepresentation {
                        llvm_type: BasicTypeEnum::StructType(repr.llvm_repr.ty),
                        size: repr.llvm_repr.size,
                        alignment: repr.llvm_repr.alignment,
                    })
                } else {
                    unreachable!()
                }
            }
            Type::Variable { .. } => unreachable!(),
            Type::Function(_, _) => {
                // This is a function object.
                Some(self.general_func_obj_ty)
            }
            Type::Primitive(PrimitiveType::Unit) => None,
            Type::Primitive(PrimitiveType::Int) => Some(AnyTypeRepresentation {
                llvm_type: BasicTypeEnum::IntType(self.codegen.context.i64_type()),
                size: 8,
                alignment: 8,
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
}

#[derive(Debug)]
pub struct Monomorphisation {
    pub types: HashSet<MonomorphisedType>,
    pub functions: HashSet<MonomorphisedFunction>,
}

impl Monomorphisation {
    /// Monomorphise the project. We start by considering the "main" function, and then
    /// track everything that it calls, so that we can work out which concrete type parameters
    /// are used.
    pub fn new(mir: &ProjectMIR) -> Self {
        let mut mono = Self {
            types: HashSet::new(),
            functions: HashSet::new(),
        };

        mono.track_def(
            mir,
            mir.entry_point.clone(),
            MonomorphisationParameters {
                type_parameters: Vec::new(),
            },
            true,
            Vec::new(),
        );

        mono
    }

    /// Assuming that this definition has the given possible monomorphisation parameters, track further required
    /// monomorphisation.
    fn track_def(
        &mut self,
        mir: &ProjectMIR,
        func: QualifiedName,
        mono: MonomorphisationParameters,
        direct: bool,
        curry_steps: Vec<u64>,
    ) {
        let def = &mir.files[&func.source_file].definitions[&func.name];
        if self.functions.insert(MonomorphisedFunction {
            func: func.clone(),
            mono: mono.clone(),
            curry_steps: curry_steps.clone(),
            direct,
        }) {
            // Work out what functions are called (and what types are referenced) by this function.
            for info in def.local_variable_names.values() {
                let ty = replace_type_variables(
                    info.ty.clone(),
                    &def.type_variables,
                    &mono.type_parameters,
                );
                self.track_type(ty);
            }

            if let DefinitionBodyM::PatternMatch(cfg) = &def.body {
                for block in cfg.basic_blocks.values() {
                    for stmt in &block.statements {
                        match &stmt.kind {
                            StatementKind::InvokeFunction {
                                name,
                                type_variables,
                                ..
                            } => {
                                self.track_def(
                                    mir,
                                    name.clone(),
                                    MonomorphisationParameters {
                                        type_parameters: type_variables.clone(),
                                    },
                                    true,
                                    Vec::new(),
                                );
                            }
                            StatementKind::ConstructFunctionObject {
                                name,
                                type_variables,
                                curry_steps,
                                ..
                            } => {
                                self.track_def(
                                    mir,
                                    name.clone(),
                                    MonomorphisationParameters {
                                        type_parameters: type_variables.clone(),
                                    },
                                    true,
                                    curry_steps.clone(),
                                );
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Add all functions that are generated by partially applying this one.
            let mut next_curry_steps = curry_steps;
            while !next_curry_steps.is_empty() {
                self.track_def(
                    mir,
                    func.clone(),
                    mono.clone(),
                    false,
                    next_curry_steps.clone(),
                );
                next_curry_steps.remove(0);
            }
        }
    }

    fn track_type(&mut self, ty: Type) {
        if let Type::Named { name, parameters } = ty {
            self.types.insert(MonomorphisedType {
                name,
                mono: MonomorphisationParameters {
                    type_parameters: parameters,
                },
            });
        }
    }
}

/// Sorts a set of types based on a "used-in" relationship.
/// If a type A is used in a type B with no pointer indirection, then we say "A <= B".
/// We consider "A <= A" to be false in general.
/// In particular, if "A <= B" then the size of A is not greater than the size of B (up to alignment and LLVM's optimisations).
///
/// This produces a directed graph of types, essentially representing a preordered set of types
/// If we have a cycle, then we must introduce a level of indirection (explicit heap allocation) at some point in the cycle,
/// so that data structures do not have infinite size. We detect cycles using Tarjan's strongly
/// connected components algorithm.
fn sort_types(
    types: HashSet<MonomorphisedType>,
    index: &ProjectIndex,
) -> Vec<IndirectedMonomorphisedType> {
    // First, construct the directed graph.
    let mut types_to_indices = HashMap::new();
    let mut vertices = Vec::new();
    for (i, ty) in types.into_iter().enumerate() {
        vertices.push(ty.clone());
        types_to_indices.insert(ty, i);
    }

    let mut graph = DirectedGraph {
        vertices,
        edges: HashMap::new(),
    };

    for (vertex_index, vertex) in graph.vertices.iter().enumerate() {
        // Get the index entry for this type, and add edges to the graph based on which types are used in this type.
        let edges = &mut graph.edges;
        let mut fill_graph = |type_ctor: &TypeConstructorI, type_params| {
            for (_field_name, field_type) in &type_ctor.fields {
                let concrete_field_type = replace_type_variables(
                    field_type.clone(),
                    type_params,
                    &vertex.mono.type_parameters,
                );
                if let Type::Named {
                    name: field_type_name,
                    parameters: field_type_parameters,
                } = concrete_field_type
                {
                    let monomorphised_field_type = MonomorphisedType {
                        name: field_type_name,
                        mono: MonomorphisationParameters {
                            type_parameters: field_type_parameters,
                        },
                    };
                    // Find this other type in the graph, and connect them with an edge.
                    // The edge leads from the child vertex to the parent vertex, so that the topological sort
                    // gives all child vertices before all parent vertices.
                    let child_vertex_index =
                        *types_to_indices.get(&monomorphised_field_type).unwrap();
                    edges
                        .entry(child_vertex_index)
                        .or_default()
                        .insert(vertex_index);
                }
            }
        };

        match &index[&vertex.name.source_file].types[&vertex.name.name].decl_type {
            TypeDeclarationTypeI::Data(datai) => {
                fill_graph(&datai.type_ctor, &datai.type_params);
            }
            TypeDeclarationTypeI::Enum(enumi) => {
                for variant in &enumi.variants {
                    fill_graph(&variant.type_ctor, &enumi.type_params);
                }
            }
        }
    }

    // Now that we have the graph, let's run Tarjan's algorithm on it to find any cycles.
    fix_cycles(graph)
}

/// Given a graph of types (ordered by a "used-in" relation), fix the types so that
/// no cycles occur. Then output the sorted list of types. This uses Kahn's topological sorting algorithm.
fn fix_cycles(graph: DirectedGraph<MonomorphisedType>) -> Vec<IndirectedMonomorphisedType> {
    let components = graph.strongly_connected_components();

    // Fix the cycles in each child component by adding one heap allocation if a cycle was detected.
    let mut components = DirectedGraph {
        vertices: components
            .vertices
            .into_iter()
            .map(|mut component| {
                if component.vertices.len() > 1 {
                    // There was a cycle. So add one heap indirection, and then try again.
                    fix_cycles(add_heap_indirection(component))
                } else {
                    vec![IndirectedMonomorphisedType {
                        ty: component.vertices.pop().unwrap(),
                        indirected: Vec::new(),
                    }]
                }
            })
            .collect(),
        edges: components.edges,
    };

    // Find a list of start edges `s`.
    // Make a cache of incoming edges for each vertex.
    let mut incoming_edges = HashMap::<usize, Vec<usize>>::new();
    for (&source, targets) in &components.edges {
        for &target in targets {
            incoming_edges.entry(target).or_default().push(source);
        }
    }
    // We've worked out the set of all strongly connected components that have an edge pointing to them.
    // Then the set of start nodes is the complement of this set of nodes that are pointed towards.
    let mut s = (0..components.vertices.len())
        .into_iter()
        .filter(|i| !incoming_edges.contains_key(i))
        .collect::<Vec<_>>();

    // From now, we don't care about the values of the strongly connected components, so we take them out of the graph.
    let mut components_by_index = components
        .vertices
        .into_iter()
        .enumerate()
        .collect::<HashMap<_, _>>();

    let mut l = Vec::new();

    while let Some(node) = s.pop() {
        l.extend(components_by_index.remove(&node).unwrap());
        // The `flatten` coalesces the HashSet and the Option.
        for target in components.edges.remove(&node).into_iter().flatten() {
            // Check if `target` has any incoming edges.
            let incoming_edges = incoming_edges.entry(target).or_default();
            if let Some(source_idx) =
                incoming_edges
                    .iter()
                    .enumerate()
                    .find_map(|(i, incoming_edge)| {
                        if *incoming_edge == node {
                            Some(i)
                        } else {
                            None
                        }
                    })
            {
                incoming_edges.remove(source_idx);
            }
            if incoming_edges.is_empty() {
                // Insert this target node into the set `s`.
                s.push(target);
            }
        }
    }

    l
}

/// Add one heap indirection to the given strongly connected graph to try to break a cycle.
fn add_heap_indirection(
    graph: DirectedGraph<MonomorphisedType>,
) -> DirectedGraph<MonomorphisedType> {
    unimplemented!()
}

/// A directed graph on an owned set of vertices.
#[derive(Debug)]
struct DirectedGraph<V> {
    /// When inserting a new vertex into a graph, always push it to the back of this list.
    /// This ensures we won't disturb existing edges.
    vertices: Vec<V>,
    /// Edges are pairs of vertices: the "from" and the "to".
    edges: HashMap<usize, HashSet<usize>>,
}

impl<V> DirectedGraph<V> {
    /// Work out which subsets of this graph are strongly connected, using Tarjan's
    /// strongly connected components algorithm.
    /// The output graph is a directed acyclic graph where the vertices are the strongly connected components of the original graph.
    pub fn strongly_connected_components(self) -> DirectedGraph<DirectedGraph<V>> {
        let strongly_connected_components = Tarjan::run_algorithm(self.vertices.len(), &self.edges);
        // Store which component each vertex belongs to.
        let vertex_index_to_component_number = strongly_connected_components
            .iter()
            .enumerate()
            .map(|(i, set)| set.iter().map(move |elem| (*elem, i)))
            .flatten()
            .collect::<HashMap<usize, usize>>();

        // Now, take the list of strongly connected components and convert them into vertices on this new graph.
        let mut output = DirectedGraph {
            vertices: strongly_connected_components
                .into_iter()
                .map(|vertex_indices| DirectedGraph {
                    vertices: vertex_indices.into_iter().collect(),
                    edges: HashMap::new(),
                })
                .collect(),
            edges: HashMap::new(),
        };

        // Re-insert all the edges of the original graph.
        for (source, targets) in &self.edges {
            let source_component = *vertex_index_to_component_number.get(source).unwrap();
            for target in targets {
                let target_component = *vertex_index_to_component_number.get(target).unwrap();
                if source_component == target_component {
                    // Insert the edge inside the component's graph.
                    output.vertices[source_component]
                        .edges
                        .entry(*source)
                        .or_default()
                        .insert(*target);
                } else {
                    // Insert the edge between the two component graphs.
                    output
                        .edges
                        .entry(source_component)
                        .or_default()
                        .insert(target_component);
                }
            }
        }

        // Now, convert each vertex index back into the vertex it represents.
        let mut vertices = self
            .vertices
            .into_iter()
            .enumerate()
            .collect::<HashMap<_, _>>();

        DirectedGraph {
            vertices: output
                .vertices
                .into_iter()
                .map(|strongly_connected_component| {
                    // We'll need to re-number the edges because currently they're written in terms of the original vertex indices.
                    let local_indices = strongly_connected_component
                        .vertices
                        .iter()
                        .copied()
                        .enumerate()
                        .collect::<HashMap<_, _>>();
                    DirectedGraph {
                        vertices: strongly_connected_component
                            .vertices
                            .into_iter()
                            .map(|index| vertices.remove(&index).unwrap())
                            .collect(),
                        edges: strongly_connected_component
                            .edges
                            .into_iter()
                            .map(|(source, targets)| {
                                (
                                    *local_indices.get(&source).unwrap(),
                                    targets
                                        .into_iter()
                                        .map(|target| *local_indices.get(&target).unwrap())
                                        .collect::<HashSet<_>>(),
                                )
                            })
                            .collect(),
                    }
                })
                .collect(),
            edges: output.edges,
        }
    }
}

#[derive(Debug)]
struct Tarjan<'a> {
    graph_edges: &'a HashMap<usize, HashSet<usize>>,

    index: usize,
    stack: Vec<usize>,

    /// Stores the indices, lowest links, and whether indices are on the stack, by index.
    indices: HashMap<usize, usize>,
    low_links: HashMap<usize, usize>,
    /// If on_stack contains a vertex index v, then v is on the stack.
    on_stack: HashSet<usize>,

    /// Strongly connected components are denoted by the set of vertices that they contain.
    strongly_connected_components: Vec<HashSet<usize>>,
}

impl<'a> Tarjan<'a> {
    pub fn run_algorithm(
        num_vertices: usize,
        graph_edges: &'a HashMap<usize, HashSet<usize>>,
    ) -> Vec<HashSet<usize>> {
        let mut tarjan = Tarjan {
            graph_edges,
            index: 0,
            stack: Vec::new(),
            indices: HashMap::new(),
            low_links: HashMap::new(),
            on_stack: HashSet::new(),
            strongly_connected_components: Vec::new(),
        };

        for vertex_index in 0..num_vertices {
            if !tarjan.indices.contains_key(&vertex_index) {
                tarjan.strong_connect(vertex_index);
            }
        }

        tarjan.strongly_connected_components
    }

    fn strong_connect(&mut self, vertex_index: usize) {
        self.indices.insert(vertex_index, self.index);
        self.low_links.insert(vertex_index, self.index);
        self.index += 1;
        self.stack.push(vertex_index);

        if let Some(edges) = self.graph_edges.get(&vertex_index) {
            for &other_vertex_index in edges {
                if !self.indices.contains_key(&other_vertex_index) {
                    self.strong_connect(other_vertex_index);
                    let other_low_link = *self.low_links.get(&other_vertex_index).unwrap();
                    let low_link = self.low_links.get_mut(&vertex_index).unwrap();
                    *low_link = std::cmp::min(*low_link, other_low_link);
                } else if self.on_stack.contains(&other_vertex_index) {
                    let low_link = self.low_links.get_mut(&vertex_index).unwrap();
                    *low_link =
                        std::cmp::min(*low_link, *self.indices.get(&other_vertex_index).unwrap());
                }
            }
        }

        if *self.low_links.get_mut(&vertex_index).unwrap()
            == *self.indices.get_mut(&vertex_index).unwrap()
        {
            let mut strongly_connected_component = HashSet::new();
            loop {
                let other_vertex = self.stack.pop().unwrap();
                self.on_stack.remove(&other_vertex);
                strongly_connected_component.insert(other_vertex);
                if other_vertex == vertex_index {
                    break;
                }
            }
            self.strongly_connected_components
                .push(strongly_connected_component);
        }
    }
}
