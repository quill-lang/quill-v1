//! Computes the LLVM data representation of a data or enum declaration in Quill code,
//! and generates indices for GEP calls in LLVM IR.

use std::collections::{HashMap, HashSet};

use inkwell::types::StructType;
use quill_common::name::QualifiedName;
use quill_index::DataI;
use quill_mir::{DefinitionM, ProjectMIR, StatementKind};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::codegen::CodeGenContext;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisationParameters {
    pub type_parameters: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MonomorphisedType {
    name: QualifiedName,
    mono: MonomorphisationParameters,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MonomorphisedFunction {
    func: QualifiedName,
    mono: MonomorphisationParameters,
    /// Must never contain a zero.
    curry_steps: Vec<u64>,
}

pub struct DataRepresentation<'ctx> {
    /// The LLVM representation of the data structure.
    llvm_ty: StructType<'ctx>,
    /// Maps Quill field names to the index of the field in the LLVM struct representation.
    fields: HashMap<String, FieldIndex>,
}

pub enum FieldIndex {
    /// The field is inside the struct at this position.
    Literal(i32),
    /// A pointer to the field is inside the struct at this position.
    Heap(i32),
}

impl<'ctx> DataRepresentation<'ctx> {
    fn new(codegen: &CodeGenContext<'ctx>, ty: &DataI, mono: &MonomorphisationParameters) -> Self {
        unimplemented!()
    }
}

/// Stores the representations of all data/struct types in a project, post monomorphisation.
pub struct Representations<'ctx> {
    datas: HashMap<MonomorphisedType, DataRepresentation<'ctx>>,
}

impl<'ctx> Representations<'ctx> {
    pub fn new(codegen: &CodeGenContext<'ctx>, mir: &ProjectMIR) -> Self {
        let mut reprs = Self {
            datas: HashMap::new(),
        };

        // Work out all of the types that will be used.
        let mono = Monomorphisation::new(mir);
        println!("Mono: {:#?}", mono);

        reprs
    }
}

#[derive(Debug)]
struct Monomorphisation {
    types: HashSet<MonomorphisedType>,
    functions: HashSet<MonomorphisedFunction>,
}

impl Monomorphisation {
    /// Monomorphise the project. We start by considering the "main" function, and then
    /// track everything that it calls, so that we can work out which concrete type parameters
    /// are used.
    fn new(mir: &ProjectMIR) -> Self {
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
        curry_steps: Vec<u64>,
    ) {
        let def = &mir.files[&func.source_file].definitions[&func.name];
        if self.functions.insert(MonomorphisedFunction {
            func,
            mono: mono.clone(),
            curry_steps,
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

            for block in def.control_flow_graph.basic_blocks.values() {
                for stmt in &block.statements {
                    match &stmt.kind {
                        StatementKind::InvokeFunction {
                            name,
                            type_variables,
                            arguments,
                            ..
                        } => {
                            self.track_def(
                                mir,
                                name.clone(),
                                MonomorphisationParameters {
                                    type_parameters: type_variables.clone(),
                                },
                                if arguments.is_empty() {
                                    Vec::new()
                                } else {
                                    vec![arguments.len() as u64]
                                },
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
                                curry_steps.clone(),
                            );
                        }
                        _ => {}
                    }
                }
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
