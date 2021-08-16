use std::collections::{BTreeMap, BTreeSet};

use quill_index::{ProjectIndex, TypeConstructorI, TypeDeclarationTypeI};
use quill_monomorphise::{MonomorphisationParameters, MonomorphisedAspect, MonomorphisedType};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MonomorphisedItem {
    Type(MonomorphisedType),
    Aspect(MonomorphisedAspect),
}

/// A monomorphised type, where some of its fields may have a layer of heap indirection.
#[derive(Debug)]
pub(crate) struct IndirectedMonomorphisedType {
    pub ty: MonomorphisedItem,
    /// The list of types that, when included as a field inside this type, require a level of heap indirection.
    pub indirected: Vec<MonomorphisedItem>,
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
pub(crate) fn sort_types(
    types: BTreeSet<MonomorphisedType>,
    aspects: BTreeSet<MonomorphisedAspect>,
    index: &ProjectIndex,
) -> Vec<IndirectedMonomorphisedType> {
    // First, construct the directed graph.
    let mut types_to_indices = BTreeMap::new();
    let mut vertices = Vec::new();
    for (i, ty) in types
        .into_iter()
        .map(MonomorphisedItem::Type)
        .chain(aspects.into_iter().map(MonomorphisedItem::Aspect))
        .enumerate()
    {
        vertices.push(ty.clone());
        types_to_indices.insert(ty, i);
    }

    let mut graph = DirectedGraph {
        vertices,
        edges: BTreeMap::new(),
    };

    for (vertex_index, vertex) in graph.vertices.iter().enumerate() {
        // Get the index entry for this type, and add edges to the graph based on which types are used in this type.
        let edges = &mut graph.edges;
        let mut fill_graph = |type_ctor: &TypeConstructorI, type_params| {
            for (_field_name, field_type) in &type_ctor.fields {
                let concrete_field_type = replace_type_variables(
                    field_type.clone(),
                    type_params,
                    match vertex {
                        MonomorphisedItem::Type(ty) => ty.mono.type_parameters(),
                        MonomorphisedItem::Aspect(asp) => asp.mono.type_parameters(),
                    },
                );

                match concrete_field_type {
                    Type::Named {
                        name: field_type_name,
                        parameters: field_type_parameters,
                    } => {
                        let monomorphised_field_type = MonomorphisedItem::Type(MonomorphisedType {
                            name: field_type_name,
                            mono: MonomorphisationParameters::new(field_type_parameters),
                        });
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
                    Type::Impl {
                        name: field_type_name,
                        parameters: field_type_parameters,
                    } => {
                        let monomorphised_field_type =
                            MonomorphisedItem::Aspect(MonomorphisedAspect {
                                name: field_type_name,
                                mono: MonomorphisationParameters::new(field_type_parameters),
                            });
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
                    _ => {}
                }
            }
        };

        match vertex {
            MonomorphisedItem::Type(ty) => match &index.type_decl(&ty.name).decl_type {
                TypeDeclarationTypeI::Data(datai) => {
                    fill_graph(&datai.type_ctor, &datai.type_params);
                }
                TypeDeclarationTypeI::Enum(enumi) => {
                    for variant in &enumi.variants {
                        fill_graph(&variant.type_ctor, &enumi.type_params);
                    }
                }
            },
            MonomorphisedItem::Aspect(asp) => {
                let aspect = index.aspect(&asp.name);
                // Make a fake type constructor for the aspect.
                let type_ctor = TypeConstructorI {
                    fields: aspect
                        .definitions
                        .iter()
                        .map(|def| (def.name.clone(), def.symbol_type.clone()))
                        .collect(),
                };
                fill_graph(&type_ctor, &aspect.type_variables);
            }
        }
    }

    // Now that we have the graph, let's run Tarjan's algorithm on it to find any cycles.
    let graph = DirectedGraph {
        vertices: graph
            .vertices
            .into_iter()
            .map(|ty| IndirectedMonomorphisedType {
                ty,
                indirected: Vec::new(),
            })
            .collect(),
        edges: graph.edges,
    };
    fix_cycles(graph)
}

/// Given a graph of types (ordered by a "used-in" relation), fix the types so that
/// no cycles occur. Then output the sorted list of types. This uses Kahn's topological sorting algorithm.
fn fix_cycles(
    graph: DirectedGraph<IndirectedMonomorphisedType>,
) -> Vec<IndirectedMonomorphisedType> {
    let components = graph.strongly_connected_components();
    // println!("Components: {:#?}", components);

    // Fix the cycles in each child component by adding one heap allocation if a cycle was detected.
    let mut components = DirectedGraph {
        vertices: components
            .vertices
            .into_iter()
            .map(|mut component| {
                if component.edges.keys().next().is_some() {
                    // There was a cycle. So add one heap indirection, and then try again.
                    add_heap_indirection(&mut component);
                    fix_cycles(component)
                } else {
                    vec![component.vertices.pop().unwrap()]
                }
            })
            .collect(),
        edges: components.edges,
    };

    // Find a list of start edges `s`.
    // Make a cache of incoming edges for each vertex.
    let mut incoming_edges = BTreeMap::<usize, Vec<usize>>::new();
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
        .collect::<BTreeMap<_, _>>();

    let mut l = Vec::new();

    while let Some(node) = s.pop() {
        l.extend(components_by_index.remove(&node).unwrap());
        // The `flatten` coalesces the BTreeSet and the Option.
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
fn add_heap_indirection(graph: &mut DirectedGraph<IndirectedMonomorphisedType>) {
    // println!("Indirecting {:#?}", graph);
    // Choose an edge.
    let (a, b) = graph
        .edges
        .iter()
        .next()
        .map(|(k, v)| (*k, *v.iter().next().unwrap()))
        .unwrap();
    // Remove this edge from the graph.
    let set = graph.edges.get_mut(&a).unwrap();
    set.remove(&b);
    if set.is_empty() {
        graph.edges.remove(&a);
    }

    // Insert an indirection from a to b.
    let ty = graph.vertices[b].ty.clone();
    graph.vertices[a].indirected.push(ty);
}

/// A directed graph on an owned set of vertices.
#[derive(Debug)]
struct DirectedGraph<V> {
    /// When inserting a new vertex into a graph, always push it to the back of this list.
    /// This ensures we won't disturb existing edges.
    vertices: Vec<V>,
    /// Edges are pairs of vertices: the "from" and the "to".
    edges: BTreeMap<usize, BTreeSet<usize>>,
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
            .collect::<BTreeMap<usize, usize>>();

        // Now, take the list of strongly connected components and convert them into vertices on this new graph.
        let mut output = DirectedGraph {
            vertices: strongly_connected_components
                .into_iter()
                .map(|vertex_indices| DirectedGraph {
                    vertices: vertex_indices.into_iter().collect(),
                    edges: BTreeMap::new(),
                })
                .collect(),
            edges: BTreeMap::new(),
        };

        // Re-insert all the edges of the original graph.
        for (source, targets) in &self.edges {
            let source_component = *vertex_index_to_component_number.get(source).unwrap();
            for target in targets {
                let target_component = *vertex_index_to_component_number.get(target).unwrap();
                if source_component == target_component {
                    // Insert the edge inside the component's graph.
                    // The indices need to be the indices of the vertices inside that graph.
                    let inner_graph = &mut output.vertices[source_component];
                    let source_idx = inner_graph
                        .vertices
                        .iter()
                        .position(|item| item == source)
                        .unwrap();
                    let target_idx = inner_graph
                        .vertices
                        .iter()
                        .position(|item| item == target)
                        .unwrap();
                    inner_graph
                        .edges
                        .entry(source_idx)
                        .or_default()
                        .insert(target_idx);
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
            .collect::<BTreeMap<_, _>>();

        DirectedGraph {
            vertices: output
                .vertices
                .into_iter()
                .map(|strongly_connected_component| DirectedGraph {
                    vertices: strongly_connected_component
                        .vertices
                        .into_iter()
                        .map(|index| vertices.remove(&index).unwrap())
                        .collect(),
                    edges: strongly_connected_component.edges,
                })
                .collect(),
            edges: output.edges,
        }
    }
}

#[derive(Debug)]
struct Tarjan<'a> {
    graph_edges: &'a BTreeMap<usize, BTreeSet<usize>>,

    index: usize,
    stack: Vec<usize>,

    /// Stores the indices, lowest links, and whether indices are on the stack, by index.
    indices: BTreeMap<usize, usize>,
    low_links: BTreeMap<usize, usize>,
    /// If on_stack contains a vertex index v, then v is on the stack.
    on_stack: BTreeSet<usize>,

    /// Strongly connected components are denoted by the set of vertices that they contain.
    strongly_connected_components: Vec<BTreeSet<usize>>,
}

impl<'a> Tarjan<'a> {
    pub fn run_algorithm(
        num_vertices: usize,
        graph_edges: &'a BTreeMap<usize, BTreeSet<usize>>,
    ) -> Vec<BTreeSet<usize>> {
        let mut tarjan = Tarjan {
            graph_edges,
            index: 0,
            stack: Vec::new(),
            indices: BTreeMap::new(),
            low_links: BTreeMap::new(),
            on_stack: BTreeSet::new(),
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
            let mut strongly_connected_component = BTreeSet::new();
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
