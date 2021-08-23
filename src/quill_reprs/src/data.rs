//! Utilities for representations of data types and enum types.

use std::collections::{BTreeMap, BTreeSet};

use quill_common::location::{Range, SourceFileIdentifier};
use quill_index::{EnumI, TypeConstructorI, TypeParameter};
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::replace_type_variables;

use crate::{sort_types::MonomorphisedItem, Representations};
use quill_monomorphise::monomorphisation::{
    MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType,
};

#[derive(Debug, Clone)]
pub struct DataRepresentation {
    /// Where in the file was this type defined?
    pub range: Range,
    pub file: SourceFileIdentifier,
    pub name: String,

    /// Maps Quill field names to the index of the field in the struct representation,
    /// if the field had a representation.
    /// If this contains *any* fields, we say that this data type "has a representation".
    field_indices: BTreeMap<String, FieldIndex>,
    /// Contains the types of *every* field in this data type,
    /// regardless if it has a representation or not.
    field_types: BTreeMap<String, Type>,
}

#[derive(Debug, Copy, Clone)]
pub enum FieldIndex {
    /// The field is inside the struct at this position.
    Literal(u32),
    /// A pointer to the field is inside the struct at this position.
    Heap(u32),
}

impl PartialOrd for FieldIndex {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for FieldIndex {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let i = match self {
            FieldIndex::Literal(i) | FieldIndex::Heap(i) => i,
        };
        let j = match other {
            FieldIndex::Literal(j) | FieldIndex::Heap(j) => j,
        };
        i.cmp(j)
    }
}

impl PartialEq for FieldIndex {
    fn eq(&self, other: &Self) -> bool {
        let i = match self {
            FieldIndex::Literal(i) | FieldIndex::Heap(i) => i,
        };
        let j = match other {
            FieldIndex::Literal(j) | FieldIndex::Heap(j) => j,
        };
        i == j
    }
}

impl Eq for FieldIndex {}

impl DataRepresentation {
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
pub struct EnumRepresentation {
    pub mono: MonomorphisedType,
    pub range: Range,
    /// Maps variant names to data representations of the enum variants.
    /// If a discriminant is required in the data representation, it will have field name `.discriminant`.
    pub variants: BTreeMap<String, DataRepresentation>,
    /// The discriminant values associated with each variant, if there is a discriminant.
    pub variant_discriminants: BTreeMap<String, u64>,
}

impl EnumRepresentation {
    /// By this point, `reprs` should contain the representations of all (non-indirected) fields in this enum type.
    pub fn new(
        reprs: &Representations,
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

        let variant_discriminants = ty
            .variants
            .iter()
            .enumerate()
            .map(|(i, variant)| (variant.name.name.clone(), i as u64))
            .collect::<BTreeMap<_, _>>();

        EnumRepresentation {
            mono: mono.clone(),
            range: ty.range,
            variants,
            variant_discriminants,
        }
    }
}

pub struct DataRepresentationBuilder<'a> {
    reprs: &'a Representations,

    field_indices: BTreeMap<String, FieldIndex>,
    field_types: BTreeMap<String, Type>,

    /// If a field's name is in this set, it can be accessed only behind a heap pointer.
    indirect_fields: BTreeSet<String>,
}

impl<'a> DataRepresentationBuilder<'a> {
    pub fn new(reprs: &'a Representations) -> Self {
        Self {
            reprs,
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
            self.field_indices.insert(
                field_name,
                FieldIndex::Heap(self.field_indices.len() as u32),
            );
        } else if self.reprs.has_repr(replace_type_variables(
            field_type,
            type_params,
            mono.type_parameters(),
        )) {
            self.field_indices.insert(
                field_name,
                FieldIndex::Literal(self.field_indices.len() as u32),
            );
        } else {
            // This field had no representation.
        }
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
    ) -> DataRepresentation {
        DataRepresentation {
            range,
            field_indices: self.field_indices,
            field_types: self.field_types,
            file: file.clone(),
            name,
        }
    }
}
