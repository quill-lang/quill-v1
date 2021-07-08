use std::{collections::HashSet, fmt::Display};

use inkwell::{
    types::{BasicTypeEnum, FunctionType},
    AddressSpace,
};
use quill_common::name::QualifiedName;
use quill_mir::{
    mir::{ArgumentIndex, DefinitionBodyM, LocalVariableName, StatementKind},
    ProjectMIR,
};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::{
    codegen::CodeGenContext,
    repr::{
        any_type::AnyTypeRepresentation,
        data::{DataRepresentation, DataRepresentationBuilder, FieldIndex},
        Representations,
    },
};

#[derive(Debug)]
pub struct Monomorphisation {
    pub types: HashSet<MonomorphisedType>,
    pub functions: HashSet<MonomorphisedFunction>,
    /// Tracks which monomorphisations of aspects have been used.
    /// This does *not* track which impls have been used.
    pub aspects: HashSet<MonomorphisedAspect>,
}

impl Monomorphisation {
    /// Monomorphise the project. We start by considering the "main" function, and then
    /// track everything that it calls, so that we can work out which concrete type parameters
    /// are used.
    pub fn new(mir: &ProjectMIR) -> Self {
        let mut mono = Self {
            types: HashSet::new(),
            functions: HashSet::new(),
            aspects: HashSet::new(),
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

        // println!("Mono: {:#?}", mono);

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
                                        type_parameters: type_variables
                                            .iter()
                                            .cloned()
                                            .map(|ty| {
                                                replace_type_variables(
                                                    ty,
                                                    &def.type_variables,
                                                    &mono.type_parameters,
                                                )
                                            })
                                            .collect(),
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
                                        type_parameters: type_variables
                                            .iter()
                                            .cloned()
                                            .map(|ty| {
                                                replace_type_variables(
                                                    ty,
                                                    &def.type_variables,
                                                    &mono.type_parameters,
                                                )
                                            })
                                            .collect(),
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
        match ty {
            Type::Named { name, parameters } => {
                self.types.insert(MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters {
                        type_parameters: parameters,
                    },
                });
            }
            Type::Impl { name, parameters } => {
                self.aspects.insert(MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters {
                        type_parameters: parameters,
                    },
                });
            }
            _ => {}
        }
    }
}

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
        write!(f, "/{:?}", self.curry_steps)?;
        if self.direct {
            write!(f, "d")
        } else {
            write!(f, "i")
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisedAspect {
    pub name: QualifiedName,
    pub mono: MonomorphisationParameters,
}

impl Display for MonomorphisedAspect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a/{}", self.name)?;
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
            write!(f, "/{}", last)?;
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
        let function_object = if let Some(repr) = reprs.get_fobj(&descriptor) {
            repr.clone()
        } else {
            let mut builder = DataRepresentationBuilder::new(reprs);
            // Add the function pointer as the first field.
            builder.add_field_raw(
                ".fptr".to_string(),
                Some(AnyTypeRepresentation::new(
                    codegen,
                    codegen
                        .context
                        .i8_type()
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                    reprs.general_func_obj_ty.di_type,
                )),
            );
            // Add the copy function as the second field.
            builder.add_field_raw(
                ".copy".to_string(),
                Some(AnyTypeRepresentation::new(
                    codegen,
                    codegen
                        .context
                        .i8_type()
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                    reprs.general_func_obj_ty.di_type,
                )),
            );
            // Add the drop function as the third field.
            builder.add_field_raw(
                ".drop".to_string(),
                Some(AnyTypeRepresentation::new(
                    codegen,
                    codegen
                        .context
                        .i8_type()
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                    reprs.general_func_obj_ty.di_type,
                )),
            );
            // Add only the arguments not pertaining to the last currying step.
            for i in 0..def.arity - self.curry_steps.last().copied().unwrap_or(0) {
                if let Some(repr) = arg_repr_indices[i as usize].map(|i| args_with_reprs[i]) {
                    builder.add_field_raw(format!("field_{}", i), Some(repr));
                }
            }

            let repr = builder.build(
                &self.func.source_file,
                self.func.range,
                descriptor.to_string(),
            );

            // Now, define all the relevant copy and drop functions for this function object.
            // We need to make a copy/drop function for every possible amount of fields stored in this function object.
            for fields_stored in 0..=def.arity - self.curry_steps.last().copied().unwrap_or(0) {
                // Generate the drop function.
                let func = codegen.module.add_function(
                    &format!("drop/{}#{}", descriptor.to_string(), fields_stored),
                    codegen
                        .context
                        .void_type()
                        .fn_type(&[repr.llvm_repr.as_ref().unwrap().ty.into()], false),
                    None,
                );
                let block = codegen.context.append_basic_block(func, "drop");
                codegen.builder.position_at_end(block);
                codegen.builder.unset_current_debug_location();

                let value = func.get_first_param().unwrap();
                let ptr = codegen
                    .builder
                    .build_alloca(value.get_type(), "value_to_drop");
                codegen.builder.build_store(ptr, value);
                for heap_field in repr.field_names_on_heap() {
                    // Check if this field has been assigned, given that we've assigned to the first `fields_stored` fields.
                    let assigned = if let FieldIndex::Heap(i) = repr.field_indices()[heap_field] {
                        i < fields_stored as u32
                    } else {
                        false
                    };
                    if assigned {
                        let ptr_to_field = repr.load(codegen, reprs, ptr, heap_field).unwrap();
                        let ty = repr.field_ty(heap_field).unwrap().clone();
                        reprs.drop_ptr(ty, ptr_to_field);
                    }
                }
                repr.free_fields(codegen, ptr);
                codegen.builder.build_return(None);

                // Generate the copy function.
                let func = codegen.module.add_function(
                    &format!("copy/{}#{}", descriptor.to_string(), fields_stored),
                    repr.llvm_repr.as_ref().unwrap().ty.fn_type(
                        &[repr
                            .llvm_repr
                            .as_ref()
                            .unwrap()
                            .ty
                            .ptr_type(AddressSpace::Generic)
                            .into()],
                        false,
                    ),
                    None,
                );
                let block = codegen.context.append_basic_block(func, "copy");
                codegen.builder.position_at_end(block);
                codegen.builder.unset_current_debug_location();
                codegen.builder.build_unreachable();
                // TODO: actually generate the copy function.
            }

            reprs.insert_fobj(descriptor, repr.clone());
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
