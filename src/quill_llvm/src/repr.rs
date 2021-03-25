//! Computes the LLVM data representation of a data or enum declaration in Quill code,
//! and generates indices for GEP calls in LLVM IR.

use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use inkwell::types::{BasicTypeEnum, StructType};
use quill_common::name::QualifiedName;
use quill_index::{EnumI, ProjectIndex, TypeConstructorI, TypeDeclarationTypeI, TypeParameter};
use quill_mir::{ProjectMIR, StatementKind};
use quill_type::{PrimitiveType, Type};
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

impl Display for MonomorphisedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
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
struct MonomorphisedFunction {
    func: QualifiedName,
    mono: MonomorphisationParameters,
    /// Must never contain a zero.
    curry_steps: Vec<u64>,
}

pub enum FieldIndex {
    /// The field is inside the struct at this position.
    Literal(i32),
    /// A pointer to the field is inside the struct at this position.
    Heap(i32),
}

pub struct LLVMRepresentation<'ctx> {
    ty: StructType<'ctx>,
    size: u32,
    alignment: u32,
}

pub struct DataRepresentation<'ctx> {
    /// The LLVM representation of the data structure, if it requires a representation at all.
    llvm_repr: Option<LLVMRepresentation<'ctx>>,
    /// Maps Quill field names to the index of the field in the LLVM struct representation.
    fields: HashMap<String, FieldIndex>,
}

pub struct EnumRepresentation<'ctx> {
    /// The LLVM representation of the enum structure.
    llvm_repr: LLVMRepresentation<'ctx>,
    /// Maps variant names to data representations of the enum variants.
    /// If a discriminant is required in the data representation, it will have field name `.discriminant`.
    variants: HashMap<String, DataRepresentation<'ctx>>,
}

struct DataRepresentationBuilder<'a, 'ctx> {
    reprs: &'a Representations<'a, 'ctx>,

    llvm_field_types: Vec<BasicTypeEnum<'ctx>>,
    fields: HashMap<String, FieldIndex>,

    size: u32,
    alignment: u32,
}

impl<'a, 'ctx> DataRepresentationBuilder<'a, 'ctx> {
    fn new(reprs: &'a Representations<'a, 'ctx>) -> Self {
        Self {
            reprs,
            llvm_field_types: Vec::new(),
            fields: HashMap::new(),
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
        if let Some(repr) = self.reprs.repr(replace_type_variables(
            field_type,
            &type_params,
            &mono.type_parameters,
        )) {
            self.llvm_field_types.push(repr.llvm_type);
            self.fields.insert(
                field_name,
                FieldIndex::Literal(self.llvm_field_types.len() as i32),
            );

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
        } else {
            // This field had no representation.
        }
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
    fn build(self, name: &str) -> DataRepresentation<'ctx> {
        if self.llvm_field_types.is_empty() {
            DataRepresentation {
                llvm_repr: None,
                fields: self.fields,
            }
        } else {
            let llvm_ty = self.reprs.codegen.context.opaque_struct_type(name);
            llvm_ty.set_body(&self.llvm_field_types, false);
            println!("Created {:?}", llvm_ty);
            DataRepresentation {
                llvm_repr: Some(LLVMRepresentation {
                    ty: llvm_ty,
                    size: self.size,
                    alignment: self.alignment,
                }),
                fields: self.fields,
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
                    builder.build(&format!("{}@{}", mono, variant.name.name)),
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
            BasicTypeEnum::IntType(codegen.context.i32_type()),
            BasicTypeEnum::ArrayType(codegen.context.i8_type().array_type(size - 4)),
        ];
        let llvm_ty = codegen.context.struct_type(&llvm_field_types, false);

        EnumRepresentation {
            llvm_repr: LLVMRepresentation {
                ty: llvm_ty,
                size,
                alignment,
            },
            variants,
        }
    }
}

/// Stores the representations of all data/struct types in a project, post monomorphisation.
pub struct Representations<'a, 'ctx> {
    codegen: &'a CodeGenContext<'ctx>,
    datas: HashMap<MonomorphisedType, DataRepresentation<'ctx>>,
    enums: HashMap<MonomorphisedType, EnumRepresentation<'ctx>>,
}

pub struct AnyTypeRepresentation<'ctx> {
    pub llvm_type: BasicTypeEnum<'ctx>,
    pub size: u32,
    pub alignment: u32,
}

impl<'a, 'ctx> Representations<'a, 'ctx> {
    pub fn new(codegen: &'a CodeGenContext<'ctx>, mir: &ProjectMIR, index: &ProjectIndex) -> Self {
        let mut reprs = Self {
            codegen,
            datas: HashMap::new(),
            enums: HashMap::new(),
        };

        // Work out all of the types that will be used.
        let mono = Monomorphisation::new(mir);
        // println!("Mono: {:#?}", mono);

        // Sort the types according to what types are used in what other types.
        // After this step, heap indirections have been added so the exact size of each type is known.
        let sorted_types = sort_types(mono.types, index);
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
                    let repr = builder.build(&mono_ty.ty.to_string());
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
            Type::Function(_, _) => unimplemented!(),
            Type::Primitive(PrimitiveType::Unit) => None,
            Type::Primitive(PrimitiveType::Int) => Some(AnyTypeRepresentation {
                llvm_type: BasicTypeEnum::IntType(self.codegen.context.i64_type()),
                size: 8,
                alignment: 8,
            }),
        }
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
