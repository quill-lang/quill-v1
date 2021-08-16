use std::collections::{BTreeMap, BTreeSet};

use quill_index::{ProjectIndex, TypeConstructorI, TypeDeclarationTypeI};
use quill_monomorphise::monomorphisation::{
    FunctionObjectDescriptor, MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType,
};
use quill_type::{PrimitiveType, Type};
use sort_types::IndirectedMonomorphisedType;

use crate::sort_types::MonomorphisedItem;

use self::data::{DataRepresentation, DataRepresentationBuilder, EnumRepresentation};

pub mod data;
pub mod sort_types;

/// Stores the representations of all data/struct types in a project, post monomorphisation.
pub struct Representations {
    pub datas: BTreeMap<MonomorphisedType, DataRepresentation>,
    pub enums: BTreeMap<MonomorphisedType, EnumRepresentation>,
    pub func_objects: BTreeMap<FunctionObjectDescriptor, DataRepresentation>,
    /// The representation of an arbitrary impl for a given aspect.
    pub aspects: BTreeMap<MonomorphisedAspect, DataRepresentation>,
    pub sorted_types: Vec<IndirectedMonomorphisedType>,
}

impl Representations {
    pub fn new(
        index: &ProjectIndex,
        mono_types: BTreeSet<MonomorphisedType>,
        mono_aspects: BTreeSet<MonomorphisedAspect>,
    ) -> Self {
        // Sort the types according to what types are used in what other types.
        // After this step, heap indirections have been added so the exact size of each type is known.
        let sorted_types = crate::sort_types::sort_types(mono_types, mono_aspects, index);
        // println!("Sorted: {:#?}", sorted_types);

        let mut reprs = Self {
            datas: BTreeMap::new(),
            enums: BTreeMap::new(),
            func_objects: BTreeMap::new(),
            aspects: BTreeMap::new(),
            sorted_types: sorted_types.clone(),
        };

        for mono_ty in sorted_types {
            match mono_ty.ty {
                MonomorphisedItem::Type(ty) => {
                    let decl = index.type_decl(&ty.name);
                    match &decl.decl_type {
                        TypeDeclarationTypeI::Data(datai) => {
                            let mut builder = DataRepresentationBuilder::new(&reprs);
                            builder.add_fields(
                                &datai.type_ctor,
                                &datai.type_params,
                                &ty.mono,
                                mono_ty.indirected,
                            );
                            let repr =
                                builder.build(&ty.name.source_file, ty.name.range, ty.to_string());
                            reprs.datas.insert(ty, repr);
                        }
                        TypeDeclarationTypeI::Enum(enumi) => {
                            let repr =
                                EnumRepresentation::new(&reprs, enumi, &ty, mono_ty.indirected);
                            reprs.enums.insert(ty, repr);
                        }
                    };
                }
                MonomorphisedItem::Aspect(asp) => {
                    let aspect = index.aspect(&asp.name);
                    // Make a fake type ctor for the aspect.
                    let type_ctor = TypeConstructorI {
                        fields: aspect
                            .definitions
                            .iter()
                            .map(|def| (def.name.clone(), def.symbol_type.clone()))
                            .collect(),
                    };
                    let mut builder = DataRepresentationBuilder::new(&reprs);
                    builder.add_fields(
                        &type_ctor,
                        &aspect.type_variables,
                        &asp.mono,
                        mono_ty.indirected,
                    );
                    let repr =
                        builder.build(&asp.name.source_file, asp.name.range, asp.to_string());
                    reprs.aspects.insert(asp, repr);
                }
            }
        }

        reprs
    }

    pub fn has_repr(&self, ty: Type) -> bool {
        match ty {
            Type::Named { name, parameters } => {
                let mono_ty = MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if let Some(repr) = self.datas.get(&mono_ty) {
                    !repr.field_indices().is_empty()
                } else if let Some(_repr) = self.enums.get(&mono_ty) {
                    // Enums have discriminants, so always have a representation.
                    true
                } else {
                    unreachable!("ty was {}", mono_ty)
                }
            }
            Type::Variable { .. } => unreachable!(),
            Type::Function(_, _) => {
                // This is a function object.
                true
            }
            Type::Primitive(PrimitiveType::Unit) => false,
            Type::Primitive(_) => true,
            // Borrows only have a representation if their borrowed type has a representation.
            Type::Borrow { ty, .. } => self.has_repr(*ty),
            Type::Impl { name, parameters } => {
                let mono_asp = MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                };
                if let Some(repr) = self.aspects.get(&mono_asp) {
                    !repr.field_indices().is_empty()
                } else {
                    unreachable!("ty was {}", mono_asp)
                }
            }
        }
    }

    pub fn get_data(&self, descriptor: &MonomorphisedType) -> Option<&DataRepresentation> {
        self.datas.get(descriptor)
    }

    pub fn get_enum(&self, descriptor: &MonomorphisedType) -> Option<&EnumRepresentation> {
        self.enums.get(descriptor)
    }

    pub fn get_fobj(&self, descriptor: &FunctionObjectDescriptor) -> Option<&DataRepresentation> {
        self.func_objects.get(descriptor)
    }

    pub fn insert_fobj(&mut self, descriptor: FunctionObjectDescriptor, fobj: DataRepresentation) {
        self.func_objects.insert(descriptor, fobj);
    }

    pub fn get_aspect(&self, descriptor: &MonomorphisedAspect) -> Option<&DataRepresentation> {
        self.aspects.get(descriptor)
    }
}
