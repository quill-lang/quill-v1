//! This module contains the mid-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

use std::collections::HashMap;

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_parser::NameP;
use quill_type::Type;
use quill_type_deduce::type_check::{Definition, Pattern, SourceFileHIR};

/// A parsed, type checked, and borrow checked source file.
#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, DefinitionM>,
}

#[derive(Debug)]
pub struct UnnamedLocalVariableId(pub u64);
#[derive(Debug)]
pub struct BasicBlockId(pub u64);

/// A local variable is a value which can be operated on by functions and expressions.
/// Other objects, such as symbols in global scope, must be instanced as local variables
/// before being operated on. This allows the borrow checker and the code translator
/// to better understand the control flow and data flow.
#[derive(Debug)]
pub enum LocalVariableName {
    /// An argument starts as being 'owned'.
    /// Parts of arguments, such as pattern-matched components, are explicitly
    /// retrieved from an argument by a MIR expression in the function body.
    Argument(String),
    /// Unnamed local variables, such as intermediate values, are given a unique ID to distinguish them.
    Unnamed(UnnamedLocalVariableId),
    /// The return value can be written to (but not read from) using this enum value.
    ReturnValue,
}

/// A definition for a symbol, i.e. a function or constant.
/// The function's type is `arg_types -> return_type`.
/// For example, if we defined a function
/// ```notrust
/// def foo: int -> int -> int {
///     foo a b = a
/// }
/// ```
/// then `arg_types` would be `[int, int]` and `return_type` would be `int`. If instead we defined it as
/// ```notrust
/// def foo: int -> int -> int {
///     foo a = \b -> a
/// }
/// ```
/// then `arg_types` would be `[int]` and `return_type` would be `int -> int`.
///
/// Further, in this struct, different pattern match cases in a function are unified into one control flow graph,
/// where the pattern matching is carried out explicitly. Local variables from each case are unified into one list.
#[derive(Debug)]
pub struct DefinitionM {
    range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<String>,
    pub arg_types: Vec<Type>,
    pub return_type: Type,
    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
}

impl Ranged for DefinitionM {
    fn range(&self) -> Range {
        self.range
    }
}

/// Information about a local variable, either explicitly or implicitly defined.
#[derive(Debug)]
pub struct LocalVariableInfo {
    /// Where was the local variable defined?
    /// If this is just an expression, then this is the range of the expression.
    pub range: Range,
    /// What is the exact type of this variable?
    pub ty: Type,
}

#[derive(Debug)]
pub struct ControlFlowGraph {
    /// Every basic block has a unique index, which is its index inside this basic blocks map.
    /// When jumping between basic blocks, we must provide the index of the target block.
    pub basic_blocks: HashMap<BasicBlockId, BasicBlock>,
}

/// A basic block is a block of code that can be executed, and may manipulate values.
/// Control flow is entirely linear inside a basic block.
/// After this basic block, we may branch to one of several places.
#[derive(Debug)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug)]
pub struct Statement {
    pub range: Range,
    pub kind: StatementKind,
}

#[derive(Debug)]
pub enum StatementKind {}

#[derive(Debug)]
pub struct Terminator {
    pub range: Range,
    pub kind: TerminatorKind,
}

#[derive(Debug)]
pub enum TerminatorKind {
    /// Works out which variant of a enum type a given local variable is.
    SwitchDiscriminator {},
}

/// Converts all expressions into control flow graphs.
pub fn to_mir(
    source_file: &SourceFileIdentifier,
    file: SourceFileHIR,
) -> DiagnosticResult<SourceFileMIR> {
    let definitions = file
        .definitions
        .into_iter()
        .map(|(def_name, def)| to_mir_def(def).map(|def| (def_name, def)))
        .collect::<DiagnosticResult<Vec<_>>>();

    definitions.map(|definitions| SourceFileMIR {
        definitions: definitions.into_iter().collect(),
    })
}

/// While we're translating a definition into MIR, this structure is passed around
/// all the expressions so that we can keep a definition-wide log of all the variables
/// we're using.
struct DefinitionTranslationContext {
    pub next_local_variable_id: UnnamedLocalVariableId,
    pub next_block_id: BasicBlockId,

    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
}

fn to_mir_def(def: Definition) -> DiagnosticResult<DefinitionM> {
    let mut ctx = DefinitionTranslationContext {
        next_local_variable_id: UnnamedLocalVariableId(0),
        next_block_id: BasicBlockId(0),
        local_variable_names: HashMap::new(),
        control_flow_graph: ControlFlowGraph {
            basic_blocks: HashMap::new(),
        },
    };

    let range = def.range();
    let type_variables = def.type_variables.clone();
    let arg_types = def.arg_types.clone();
    let return_type = def.return_type.clone();

    // Set up the pattern matching on the parameters.
    // Then, this function will create the rest of the control flow graph
    // for sub-expressions.
    setup_def_pattern_matching(def, &mut ctx);

    DiagnosticResult::ok(DefinitionM {
        range,
        type_variables,
        arg_types,
        return_type,
        local_variable_names: ctx.local_variable_names,
        control_flow_graph: ctx.control_flow_graph,
    })
}

/// Creates a control flow graph for a function definition.
fn setup_def_pattern_matching(def: Definition, ctx: &mut DefinitionTranslationContext) {
    // Begin by setting up pattern matching for the parameters.
}

// Returns a map from names of variables to their borrow statuses.
// fn cache_arg_pattern(pat: &Pattern) -> HashMap<NameP, BorrowStatus> {
//     match pat {
//         Pattern::Named(name) => {
//             let mut map = HashMap::new();
//             map.insert(name.clone(), BorrowStatus::Owned);
//             map
//         }
//         Pattern::TypeConstructor { fields, .. } => {
//             let mut map = HashMap::new();
//             for (_field_name, pat) in fields {
//                 map.extend(cache_arg_pattern(pat));
//             }
//             map
//         }
//         Pattern::Function { .. } => {
//             unreachable!("functions are forbidden in arg patterns")
//         }
//         Pattern::Unknown(_) => HashMap::new(),
//     }
// }
