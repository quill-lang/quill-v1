//! Computes the LLVM data representation of a data or enum declaration in Quill code,
//! and generates indices for GEP calls in LLVM IR.

use std::collections::{HashMap, HashSet};

use inkwell::types::StructType;
use quill_common::name::QualifiedName;
use quill_index::DataI;
use quill_mir::{DefinitionM, ProjectMIR};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

use crate::codegen::CodeGenContext;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MonomorphisationParameters {
    pub type_parameters: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MonomorphisedType {
    ty: QualifiedName,
    mono: MonomorphisationParameters,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct MonomorphisedFunction {
    func: QualifiedName,
    mono: MonomorphisationParameters,
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
    ) {
        let def = &mir.files[&func.source_file].definitions[&func.name];
        if self.functions.insert(MonomorphisedFunction {
            func,
            mono: mono.clone(),
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
        }
    }

    fn track_type(&mut self, ty: Type) {
        println!("Tracking {}", ty);
    }
}
