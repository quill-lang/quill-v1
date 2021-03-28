//! This module contains the m range: (), kind: ()id-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Display,
};

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI, TypeParameter};
use quill_parser::NameP;
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::{
    type_check::{
        Definition, Expression, ExpressionContentsGeneric, ImmediateValue, Pattern, SourceFileHIR,
    },
    TypeConstructorInvocation,
};

#[derive(Debug)]
pub struct ProjectMIR {
    pub files: HashMap<SourceFileIdentifier, SourceFileMIR>,
    /// The qualified name where the "main" function is.
    pub entry_point: QualifiedName,
}

#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, DefinitionM>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct ArgumentIndex(pub u64);
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct LocalVariableId(pub u64);
impl Display for LocalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.0)
    }
}
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct BasicBlockId(pub u64);

impl Display for BasicBlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "bb{}", self.0)
    }
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
#[derive(Debug, Clone)]
pub struct DefinitionM {
    pub range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<TypeParameter>,
    /// How many parameters must be supplied to this function? Their types are kept in the local variable names map.
    pub arity: u64,
    /// Contains argument types as well as local variable types.
    pub local_variable_names: BTreeMap<LocalVariableName, LocalVariableInfo>,
    pub return_type: Type,
    pub control_flow_graph: ControlFlowGraph,
    /// Which basic block should be entered to invoke the function?
    pub entry_point: BasicBlockId,
}

impl Ranged for DefinitionM {
    fn range(&self) -> Range {
        self.range
    }
}

impl Display for DefinitionM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "arity: {}", self.arity)?;
        writeln!(f, "entry point: {}", self.entry_point)?;

        for (var, info) in &self.local_variable_names {
            writeln!(f, "    {} >> let {}: {}", info.range, var, info)?;
        }
        for (block_id, block) in &self.control_flow_graph.basic_blocks {
            writeln!(f, "{}:", block_id)?;
            for stmt in &block.statements {
                writeln!(f, "    {}", stmt)?;
            }
            writeln!(f, "    {}", block.terminator)?;
        }

        Ok(())
    }
}

/// A local variable is a value which can be operated on by functions and expressions.
/// Other objects, such as symbols in global scope, must be instanced as local variables
/// before being operated on. This allows the borrow checker and the code translator
/// to better understand the control flow and data flow.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub enum LocalVariableName {
    /// An argument starts as being 'owned'.
    /// Parts of arguments, such as pattern-matched components, are explicitly
    /// retrieved from an argument by a MIR expression in the function body.
    Argument(ArgumentIndex),
    /// Local variables, such as intermediate values, are given a unique ID to distinguish them.
    Local(LocalVariableId),
}

impl Display for LocalVariableName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LocalVariableName::Argument(arg) => write!(f, "arg{}", arg.0),
            LocalVariableName::Local(local) => write!(f, "{}", local),
        }
    }
}

/// Information about a local variable, either explicitly or implicitly defined.
#[derive(Debug, Clone)]
pub struct LocalVariableInfo {
    /// Where was the local variable defined?
    /// If this is just an expression, then this is the range of the expression.
    pub range: Range,
    /// What is the exact type of this variable?
    pub ty: Type,
    /// If this variable had a name, what was it?
    pub name: Option<String>,
}

impl Display for LocalVariableInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ty)?;
        if let Some(name) = &self.name {
            write!(f, " named {}", name)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    next_block_id: BasicBlockId,
    /// Every basic block has a unique index, which is its index inside this basic blocks map.
    /// When jumping between basic blocks, we must provide the index of the target block.
    pub basic_blocks: BTreeMap<BasicBlockId, BasicBlock>,
}

impl ControlFlowGraph {
    /// Inserts a new basic block into the control flow graph, and returns its new unique ID.
    pub fn new_basic_block(&mut self, basic_block: BasicBlock) -> BasicBlockId {
        let id = self.next_block_id;
        self.next_block_id.0 += 1;
        self.basic_blocks.insert(id, basic_block);
        id
    }

    /// Assigns new basic block IDs to ensure we're in SSA form, only using variables and blocks after they're defined.
    /// Returns the new entry point.
    fn reorder(&mut self, entry_point: BasicBlockId) -> BasicBlockId {
        // We use a topological sort (Kahn's algorithm) to reorder basic blocks.

        // Cache some things about each block.
        // In particular, we need to know which blocks define and use which local variables, and
        // which other blocks a block can end up jumping to.
        let mut values_defined = HashMap::new();
        let mut values_used = HashMap::new();
        let mut target_blocks = HashMap::new();
        for (&node, block) in &self.basic_blocks {
            let mut block_values_defined = HashSet::new();
            let mut block_values_used = HashSet::new();
            let mut more_block_values_used = HashSet::new();

            let mut use_rvalue = |rvalue: &Rvalue| match rvalue {
                Rvalue::Use(Operand::Copy(place)) | Rvalue::Use(Operand::Move(place)) => {
                    block_values_used.insert(place.local);
                }
                _ => {}
            };

            for stmt in &block.statements {
                match &stmt.kind {
                    StatementKind::Assign { target, .. }
                    | StatementKind::InstanceSymbol { target, .. }
                    | StatementKind::Apply { target, .. }
                    | StatementKind::InvokeFunction { target, .. }
                    | StatementKind::ConstructFunctionObject { target, .. }
                    | StatementKind::ApplyFunctionObject { target, .. }
                    | StatementKind::InvokeFunctionObject { target, .. }
                    | StatementKind::CreateLambda { target, .. }
                    | StatementKind::ConstructData { target, .. } => {
                        block_values_defined.insert(*target);
                    }
                    _ => {}
                }

                match &stmt.kind {
                    StatementKind::Assign { source, .. } => {
                        use_rvalue(source);
                    }
                    StatementKind::Apply {
                        argument, function, ..
                    } => {
                        use_rvalue(argument);
                        use_rvalue(function);
                    }
                    StatementKind::InvokeFunction { arguments, .. } => {
                        for arg in arguments {
                            use_rvalue(arg);
                        }
                    }
                    StatementKind::ConstructFunctionObject {
                        curried_arguments, ..
                    } => {
                        for arg in curried_arguments {
                            use_rvalue(arg);
                        }
                    }
                    StatementKind::ApplyFunctionObject {
                        argument, function, ..
                    } => {
                        use_rvalue(argument);
                        use_rvalue(function);
                    }
                    StatementKind::InvokeFunctionObject {
                        additional_arguments,
                        ..
                    } => {
                        for arg in additional_arguments {
                            use_rvalue(arg);
                        }
                    }
                    StatementKind::ConstructData { fields, .. } => {
                        for field in fields.values() {
                            use_rvalue(field);
                        }
                    }
                    StatementKind::DropIfAlive { variable } => {
                        more_block_values_used.insert(*variable);
                    }
                    _ => {}
                }
            }

            let mut block_target_blocks = HashSet::new();
            // First, check possible places we'll jump to in the terminator.
            match &self.basic_blocks[&node].terminator.kind {
                TerminatorKind::Goto(target) => {
                    block_target_blocks.insert(*target);
                }
                TerminatorKind::SwitchDiscriminator {
                    enum_place, cases, ..
                } => {
                    block_values_used.insert(enum_place.local);
                    for target in cases.values() {
                        block_target_blocks.insert(*target);
                    }
                }
                TerminatorKind::Invalid => unreachable!(),
                TerminatorKind::Return { value } => {
                    block_values_used.insert(*value);
                }
            }

            values_defined.insert(node, block_values_defined);
            block_values_used.extend(more_block_values_used);
            values_used.insert(node, block_values_used);
            target_blocks.insert(node, block_target_blocks);
        }

        // Now that we have all this information, we can make a set of all the edges in this directed graph.
        let mut edges = HashMap::new();
        for &node in self.basic_blocks.keys() {
            let mut this_edges = HashSet::new();

            for var in values_defined[&node].iter().copied() {
                for &other_node in self.basic_blocks.keys() {
                    if values_used[&other_node].contains(&var) {
                        this_edges.insert(other_node);
                    }
                }
            }

            this_edges.extend(target_blocks[&node].iter().copied());

            edges.insert(node, this_edges);
        }

        // Now run Kahn's algorithm.
        // The set of start nodes is exactly the entry point of the function.
        let mut l = Vec::new();
        let mut s = vec![entry_point];
        while let Some(node) = s.pop() {
            l.push(node);
            // Look for each node that follows from this block.
            for following in edges.remove(&node).into_iter().flatten() {
                // Check to see if there are any other incoming edges into this following node.
                if edges
                    .values()
                    .flatten()
                    .find(|id| **id == following)
                    .is_none()
                {
                    s.push(following);
                }
            }
        }

        assert!(edges.is_empty());

        // Now, reorder the basic block IDs according to this new order in `l`.
        // This map maps from old block IDs to new block IDs.
        let block_id_map = l
            .into_iter()
            .enumerate()
            .map(|(new_id, old_id)| (old_id, BasicBlockId(new_id as u64)))
            .collect::<HashMap<_, _>>();

        // First we'll move them around in the CFG then we'll update all references to these IDs inside terminators.
        for (old_id, block) in std::mem::take(&mut self.basic_blocks) {
            self.basic_blocks.insert(block_id_map[&old_id], block);
        }
        // Now update all the references.
        for block in self.basic_blocks.values_mut() {
            match &mut block.terminator.kind {
                TerminatorKind::Goto(target) => {
                    *target = block_id_map[&target];
                }
                TerminatorKind::SwitchDiscriminator { cases, .. } => {
                    for target in cases.values_mut() {
                        *target = block_id_map[&target];
                    }
                }
                TerminatorKind::Invalid => unreachable!(),
                TerminatorKind::Return { .. } => {}
            }
        }
        block_id_map[&entry_point]
    }
}

/// A basic block is a block of code that can be executed, and may manipulate values.
/// Control flow is entirely linear inside a basic block.
/// After this basic block, we may branch to one of several places.
#[derive(Debug, Clone)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone)]
pub struct Statement {
    pub range: Range,
    pub kind: StatementKind,
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} >> {}", self.range, self.kind)
    }
}

#[derive(Debug, Clone)]
pub enum StatementKind {
    /// Moves an rvalue into a local variable.
    Assign {
        target: LocalVariableName,
        source: Rvalue,
    },
    /// Creates a local instance of a definition such as a function (or in some cases, a constant).
    /// This statement is removed by the "func_objects" pass, where curried functions are removed.
    InstanceSymbol {
        name: QualifiedName,
        type_variables: Vec<Type>,
        target: LocalVariableName,
    },
    /// Applies one argument to a function, and stores the result in a variable.
    /// This statement is removed by the "func_objects" pass, where curried functions are removed.
    Apply {
        argument: Rvalue,
        function: Rvalue,
        target: LocalVariableName,

        return_type: Type,
        argument_type: Type,
    },
    /// Invokes a function with the given arguments.
    /// This is inserted by the "func_objects" pass. MIR generation should instead try to generate InstanceSymbol
    /// and Apply statements, and this pass will convert them (where necessary) into this statement.
    InvokeFunction {
        name: QualifiedName,
        type_variables: Vec<Type>,
        target: LocalVariableName,
        arguments: Vec<Rvalue>,
    },
    /// Creates a function object which contains a function and any curried arguments. It may be later invoked by
    /// InvokeFunctionObject to execute the function with the provided arguments.
    /// `curry_steps` states the amount of arguments that are required in each step to execute the function object.
    /// In the `func_objects` pass, `curry_steps` is a list of n ones where n is the arity of the function. In later passes,
    /// the curry steps might be changed - but they will always sum to n.
    /// For example, a function `(a, b, c) -> d` with `curry_steps = [1, 1, 1]` will be represented as a chain of function objects `a -> (b -> (c -> d))`.
    /// With `curry_steps = [2, 1]`, the function will be represented as a chain of function objects `(a, b) -> (c -> d)`.
    /// This is inserted by the "func_objects" pass.
    ConstructFunctionObject {
        name: QualifiedName,
        type_variables: Vec<Type>,
        target: LocalVariableName,
        curry_steps: Vec<u64>,
        curried_arguments: Vec<Rvalue>,
    },
    /// Adds some new arguments to a function object. In actuality LLVM will reallocate a new function object.
    /// Even if we apply the last required argument to this function object, it will not pre-emptively execute the function.
    /// Function execution occurs only with the InvokeFunctionObject statement.
    /// This is inserted by the "func_objects" pass.
    ApplyFunctionObject {
        argument: Rvalue,
        function: Rvalue,
        target: LocalVariableName,
    },
    /// Invokes a function object with the arguments it contains, along with perhaps some additional arguments.
    /// This is inserted by the "func_objects" pass.
    /// The amount of additional_arguments must exactly match the number of arguments remaining in the function object.
    InvokeFunctionObject {
        func_object: Rvalue,
        target: LocalVariableName,
        additional_arguments: Vec<Rvalue>,

        return_type: Type,
        additional_argument_types: Vec<Type>,
    },
    /// Hints to LLVM that this variable's lifetime has now begun, and that we may use this variable later.
    /// This is automatically generated by the borrow checker.
    StorageLive(LocalVariableId),
    /// Hints to LLVM that we will no longer use this variable.
    /// This is automatically generated by the borrow checker.
    StorageDead(LocalVariableId),
    /// Calls the destructor for the object, and deallocates the variable's memory, if it has a destructor and it is currently alive.
    /// This is automatically inserted by the MIR generator at the end of the scope declaring a variable.
    /// Please note that a drop-if-alive instruction in MIR does not necessarily call the actual destructor, only if the object really is not moved out.
    /// In particular, the *first* MIR drop-if-alive instruction an object encounters will perform the actual drop and deallocation, any more are no-ops and will be optimised away.
    DropIfAlive { variable: LocalVariableName },
    /// Calls the destructor for the object, if it has a destructor.
    /// This is automatically generated by the borrow checker.
    /// This does not deallocate the memory containing this object.
    Drop { variable: LocalVariableName },
    /// Deallocates the memory containing this variable. Similar to a drop, but does not run the destructor code.
    /// Use this when a data structure is being destructured, meaning that we cannot call the destructor.
    /// In particular, if this variable is on the heap, this results in a `free` call, and if on the stack this is a no-op.
    /// This is automatically generated by the borrow checker.
    Free { variable: LocalVariableName },
    /// Creates a function object representing a lambda abstraction, capturing variables it uses.
    /// This will be converted into an external function.
    CreateLambda {
        ty: Type,
        params: Vec<NameP>,
        // expr: Box<Expression>,
        target: LocalVariableName,
    },
    /// Creates an object of a given type, and puts it in target.
    ConstructData {
        ty: Type,
        /// If this type was an enum, which variant should we create?
        variant: Option<String>,
        fields: HashMap<String, Rvalue>,
        target: LocalVariableName,
    },
}

impl Display for StatementKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatementKind::Assign { target, source } => write!(f, "{} = {}", target, source),
            StatementKind::Apply {
                argument,
                function,
                target,
                ..
            } => write!(f, "{} = apply {} to {}", target, argument, function),
            StatementKind::StorageLive(local) => write!(f, "live {}", local),
            StatementKind::StorageDead(local) => write!(f, "dead {}", local),
            StatementKind::DropIfAlive { variable } => {
                write!(f, "drop and free if alive {}", variable)
            }
            StatementKind::Drop { variable } => write!(f, "drop {}", variable),
            StatementKind::Free { variable } => write!(f, "free {}", variable),
            StatementKind::InstanceSymbol {
                name,
                type_variables,
                target,
            } => {
                write!(f, "{} = instance {}", target, name)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty_var in type_variables {
                        write!(f, " {}", ty_var)?;
                    }
                }
                Ok(())
            }
            StatementKind::InvokeFunction {
                name,
                type_variables,
                target,
                arguments,
            } => {
                write!(f, "{} = invoke {} ( ", target, name)?;
                for arg in arguments {
                    write!(f, "{}, ", arg)?;
                }
                write!(f, ")")?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty_var in type_variables {
                        write!(f, " {}", ty_var)?;
                    }
                }
                Ok(())
            }
            StatementKind::ConstructFunctionObject {
                name,
                type_variables,
                target,
                curry_steps,
                curried_arguments,
            } => {
                write!(f, "{} = fobj {} ( ", target, name)?;
                for arg in curried_arguments {
                    write!(f, "{}, ", arg)?;
                }
                write!(f, ")")?;
                write!(f, " curried {:?}", curry_steps)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty_var in type_variables {
                        write!(f, " {}", ty_var)?;
                    }
                }
                Ok(())
            }
            StatementKind::ApplyFunctionObject {
                argument,
                function,
                target,
            } => write!(f, "{} = apply {} to fobj {}", target, argument, function),
            StatementKind::InvokeFunctionObject {
                func_object,
                target,
                additional_arguments,
                ..
            } => {
                write!(f, "{} = invoke fobj {} ( ", target, func_object)?;
                for arg in additional_arguments {
                    write!(f, "{}, ", arg)?;
                }
                write!(f, ")")
            }
            StatementKind::CreateLambda { target, .. } => write!(f, "{} = lambda", target),
            StatementKind::ConstructData {
                ty,
                variant,
                fields,
                target,
            } => {
                write!(f, "{} = construct {}", target, ty)?;
                if let Some(variant) = variant {
                    write!(f, "::{}", variant)?;
                }
                write!(f, " with {{ ")?;
                for (field_name, rvalue) in fields {
                    write!(f, "{} = {} ", field_name, rvalue)?;
                }
                write!(f, "}}")
            }
        }
    }
}

/// A place in memory that we can read from and write to.
#[derive(Debug, Clone)]
pub struct Place {
    /// The local variable that the place originates from.
    pub local: LocalVariableName,
    /// A list of lenses that allow us to index inside this local variable into deeper and deeper nested places.
    pub projection: Vec<PlaceSegment>,
}

impl Display for Place {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.local)?;
        for proj in &self.projection {
            write!(f, "{}", proj)?;
        }
        Ok(())
    }
}

impl Place {
    pub fn new(local: LocalVariableName) -> Self {
        Place {
            local,
            projection: Vec::new(),
        }
    }

    pub fn then(mut self, segment: PlaceSegment) -> Self {
        self.projection.push(segment);
        self
    }
}

#[derive(Debug, Clone)]
pub enum PlaceSegment {
    DataField { field: String },
    EnumField { variant: String, field: String },
}

impl Display for PlaceSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceSegment::DataField { field } => write!(f, ".{}", field),
            PlaceSegment::EnumField { variant, field } => write!(f, ".<{}>.{}", variant, field),
        }
    }
}

/// Represents the use of a value that we can feed into an expression or function.
/// We can only read from (not write to) an rvalue.
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// Either a copy or a move, depending on the type.
    Use(Operand),
}

impl Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rvalue::Use(operand) => write!(f, "use {}", operand),
        }
    }
}

/// A value that we can read from.
#[derive(Debug, Clone)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(ImmediateValue),
}

impl Display for Operand {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Operand::Copy(place) => write!(f, "copy {}", place),
            Operand::Move(place) => write!(f, "move {}", place),
            Operand::Constant(constant) => write!(f, "const {}", constant),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Terminator {
    pub range: Range,
    pub kind: TerminatorKind,
}

impl Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} >> {}", self.range, self.kind)
    }
}

#[derive(Debug, Clone)]
pub enum TerminatorKind {
    /// Jump to another basic block unconditionally.
    Goto(BasicBlockId),
    /// Works out which variant of a enum type a given local variable is.
    SwitchDiscriminator {
        /// What enum are we switching on?
        enum_name: QualifiedName,
        /// Where is this enum stored?
        enum_place: Place,
        /// Maps the names of enum discriminants to the basic block ID to jump to.
        /// This map must exhaustively cover every possible enum discriminant.
        cases: HashMap<String, BasicBlockId>,
    },
    /// Used in intermediate steps, when we do not know the terminator of a block.
    /// This should never be translated into LLVM IR, the compiler should instead panic.
    Invalid,
    /// Returns a local variable.
    Return { value: LocalVariableName },
}

impl Display for TerminatorKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TerminatorKind::Goto(target) => write!(f, "goto {}", target),
            TerminatorKind::SwitchDiscriminator {
                enum_name,
                enum_place,
                cases,
                ..
            } => {
                write!(f, "switch {} as {} {{", enum_place, enum_name)?;
                for (case, id) in cases {
                    write!(f, " {} -> {},", case, id)?;
                }
                write!(f, " }}")
            }
            TerminatorKind::Invalid => write!(f, "invalid"),
            TerminatorKind::Return { value } => write!(f, "return {}", value),
        }
    }
}

/// Converts all expressions into control flow graphs.
pub fn to_mir(
    project_index: &ProjectIndex,
    file: SourceFileHIR,
) -> DiagnosticResult<SourceFileMIR> {
    let definitions = file
        .definitions
        .into_iter()
        .map(|(def_name, def)| to_mir_def(project_index, def).map(|def| (def_name, def)))
        .collect::<DiagnosticResult<Vec<_>>>();

    definitions.map(|definitions| SourceFileMIR {
        definitions: definitions.into_iter().collect(),
    })
}

/// While we're translating a definition into MIR, this structure is passed around
/// all the expressions so that we can keep a definition-wide log of all the variables
/// we're using.
struct DefinitionTranslationContext {
    next_local_variable_id: LocalVariableId,
    /// Retrieves the unique name of a named local variable.
    local_name_map: HashMap<String, LocalVariableName>,

    pub local_variable_names: BTreeMap<LocalVariableName, LocalVariableInfo>,
    pub control_flow_graph: ControlFlowGraph,
}

impl DefinitionTranslationContext {
    /// Creates a new local variable with the given information,
    /// that is by default not initialised.
    /// If `info` provides a name, the `local_name_map` is updated.
    pub fn new_local_variable(&mut self, info: LocalVariableInfo) -> LocalVariableId {
        let id = self.next_local_variable_id;
        self.next_local_variable_id.0 += 1;
        if let Some(name) = info.name.clone() {
            self.local_name_map
                .insert(name, LocalVariableName::Local(id));
        }
        self.local_variable_names
            .insert(LocalVariableName::Local(id), info);
        id
    }

    pub fn get_name_of_local(&self, local: &str) -> LocalVariableName {
        self.local_name_map[local]
    }
}

fn to_mir_def(project_index: &ProjectIndex, def: Definition) -> DiagnosticResult<DefinitionM> {
    let mut ctx = DefinitionTranslationContext {
        next_local_variable_id: LocalVariableId(0),
        local_variable_names: BTreeMap::new(),
        local_name_map: HashMap::new(),
        control_flow_graph: ControlFlowGraph {
            next_block_id: BasicBlockId(0),
            basic_blocks: BTreeMap::new(),
        },
    };

    let range = def.range();
    let type_variables = def.type_variables.clone();
    let arity = def.arg_types.len() as u64;
    let return_type = def.return_type.clone();

    for (i, ty) in def.arg_types.iter().enumerate() {
        ctx.local_variable_names.insert(
            LocalVariableName::Argument(ArgumentIndex(i as u64)),
            LocalVariableInfo {
                range,
                ty: ty.clone(),
                name: None,
            },
        );
    }

    // This function will create the rest of the control flow graph
    // for sub-expressions.
    let entry_point = create_cfg(project_index, &mut ctx, def);

    let mut def = DefinitionM {
        range,
        type_variables,
        arity,
        local_variable_names: ctx.local_variable_names,
        return_type,
        control_flow_graph: ctx.control_flow_graph,
        entry_point,
    };
    def.entry_point = def.control_flow_graph.reorder(def.entry_point);

    DiagnosticResult::ok(def)
}

/// Creates a control flow graph for a function definition.
/// Returns the basic block representing the function's entry point.
fn create_cfg(
    project_index: &ProjectIndex,
    ctx: &mut DefinitionTranslationContext,
    def: Definition,
) -> BasicBlockId {
    let range = def.range();
    let arg_types = def.arg_types;

    // Begin by creating the CFG for each case in the definition.
    let cases = def
        .cases
        .into_iter()
        .map(|case| {
            // Create a local variable for each bound variable in the pattern.
            let unwrap_patterns_blocks = case
                .arg_patterns
                .iter()
                .zip(&arg_types)
                .enumerate()
                .filter_map(|(i, (arg_pattern, arg_type))| {
                    bind_pattern_variables(
                        ctx,
                        Place::new(LocalVariableName::Argument(ArgumentIndex(i as u64))),
                        arg_pattern,
                        arg_type.clone(),
                    )
                })
                .collect::<Vec<_>>();

            let unwrap_patterns_block = chain(ctx, unwrap_patterns_blocks, range);

            // Now let's build the end of the function, specifically the code to return a value.
            let return_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator: Terminator {
                    range,
                    kind: TerminatorKind::Invalid,
                },
            });

            // Now, we can generate basic blocks for the rest of the function.
            initialise_expr(ctx, &case.replacement);
            let func = generate_expr(
                ctx,
                case.replacement,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(return_block),
                },
            );

            // Now, replace the terminator with a custom terminator that returns `function_variable` from the function.
            let return_block = ctx
                .control_flow_graph
                .basic_blocks
                .get_mut(&return_block)
                .unwrap();
            return_block.terminator = Terminator {
                range,
                kind: TerminatorKind::Return {
                    value: func.variable,
                },
            };
            // Further, we need to drop the function's arguments (if they're still alive) in this return block, and all of the block's undropped temporaries.
            for temp in func.locals_to_drop {
                return_block.statements.push(Statement {
                    range,
                    kind: StatementKind::DropIfAlive { variable: temp },
                })
            }
            for i in 0..arg_types.len() {
                return_block.statements.push(Statement {
                    range,
                    kind: StatementKind::DropIfAlive {
                        variable: LocalVariableName::Argument(ArgumentIndex(i as u64)),
                    },
                })
            }

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&unwrap_patterns_block)
                .unwrap()
                .terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(func.block),
            };

            (case.arg_patterns, unwrap_patterns_block)
        })
        .collect::<Vec<_>>();

    // Then perform the pattern matching operation on each parameter to the function, in reverse order.
    perform_match_function(project_index, ctx, range, arg_types, cases)
}

#[derive(Debug)]
struct PatternMismatch {
    place: Place,
    reason: PatternMismatchReason,
}

#[derive(Debug)]
enum PatternMismatchReason {
    EnumDiscriminant {
        /// What was the name of the enum we want to pattern match?
        enum_name: QualifiedName,
        /// Maps enum discriminant names to the indices of the patterns that are matched by this discriminant.
        /// If a case is valid for any discriminant, it is put in *every* case.
        cases: HashMap<String, Vec<usize>>,
    },
}

/// Given a list of patterns, in which place do they first (pairwise) differ, and how? If they do not differ, return None.
/// Two patterns are said to differ in a place if a different primitive value or enum variant at this place
/// could cause exactly one pattern to match.
/// `var` is the place where the variable that we will match is stored.
fn first_difference(
    project_index: &ProjectIndex,
    var: Place,
    ty: Type,
    patterns: &[Pattern],
) -> Option<PatternMismatch> {
    // Check to see what type the patterns represent.
    // Even though we already know `ty`, we do this check to see whether the *patterns* care
    // about what type it is.
    let type_name = patterns.iter().find_map(|pat| {
        if let Pattern::TypeConstructor { type_ctor, .. } = pat {
            Some(type_ctor.data_type.clone())
        } else {
            None
        }
    });

    if type_name.is_some() {
        // At least one of the patterns wants to inspect this variable, either its fields or its enum variant.
        // Check to see if the patterns represent an enum.
        let is_enum = patterns.iter().any(|pat| {
            if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                type_ctor.variant.is_some()
            } else {
                false
            }
        });

        let need_to_switch_enum = if is_enum {
            // Because (at least) one pattern referenced an enum variant, we might need to switch on this enum's discriminant.
            // In particular, if two patterns reference *different* variants, or one does *not* reference a variant,
            // then we need to switch the discriminant.
            // Sometimes this function can be called with a non-exhaustive set of patterns, if we've already excluded
            // some previous patterns. This means that it's possible that an enum variant is referenced, but we already know
            // which variant it is (we've already ruled out all other patterns).
            let mut expected_variant = None;
            let mut found_mismatch = false;
            for pat in patterns.iter() {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    if let Some(the_expected_variant) = expected_variant.take() {
                        if the_expected_variant != type_ctor.variant.as_ref().unwrap() {
                            // Two enum patterns referenced a different variant.
                            // So we need to switch on the enum discriminant.
                            found_mismatch = true;
                            break;
                        }
                    } else {
                        expected_variant = Some(type_ctor.variant.as_ref().unwrap());
                    }
                } else {
                    found_mismatch = true;
                    break;
                }
            }
            found_mismatch
        } else {
            false
        };

        if need_to_switch_enum {
            // Let's store which patterns require which discriminants.
            // First, work out the list of all discriminants for this enum.

            let enum_name = if let Type::Named { name, .. } = ty {
                name
            } else {
                unreachable!()
            };

            let mut cases = if let TypeDeclarationTypeI::Enum(enumi) =
                &project_index[&enum_name.source_file].types[&enum_name.name].decl_type
            {
                enumi
                    .variants
                    .iter()
                    .map(|variant| (variant.name.name.clone(), Vec::new()))
                    .collect::<HashMap<_, _>>()
            } else {
                unreachable!()
            };

            for (i, pat) in patterns.iter().enumerate() {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    // This case applies to exactly one discriminant.
                    cases
                        .get_mut(type_ctor.variant.as_ref().unwrap())
                        .unwrap()
                        .push(i);
                } else {
                    // This case applies to all discriminants.
                    for (_, case) in cases.iter_mut() {
                        case.push(i);
                    }
                }
            }

            Some(PatternMismatch {
                place: var,
                reason: PatternMismatchReason::EnumDiscriminant { enum_name, cases },
            })
        } else {
            // We do not need to match on the enum discriminator, so we now want to consider the first difference *inside* each pattern.
            // We check each field in the data type, and consider how (and if) the patterns differ when reasoning about this field.

            // Note that in this branch, all cases must have the same enum variant (if this is an enum, not a data type).
            // So let's work out which variant of the enum it is.
            let enum_variant = patterns.iter().find_map(|pat| {
                if let Pattern::TypeConstructor { type_ctor, .. } = pat {
                    type_ctor.variant.clone()
                } else {
                    None
                }
            });

            let fields = patterns
                .iter()
                .find_map(|pat| {
                    if let Pattern::TypeConstructor { fields, .. } = pat {
                        Some(
                            fields
                                .iter()
                                .map(|(name, ty, _pat)| (name.name.clone(), ty.clone()))
                                .collect::<Vec<_>>(),
                        )
                    } else {
                        None
                    }
                })
                .unwrap();

            for (field_name, field_ty) in fields {
                // Do the patterns differ in this field?
                // First, let's store the pattern that each case provides for each field.
                // If the pattern was `_` or named (e.g. `a`), then the field is not matched;
                // in this case we assume that the field's pattern is `_`.
                let field_patterns = patterns
                    .iter()
                    .map(|pat| {
                        if let Pattern::TypeConstructor { fields, .. } = pat {
                            fields
                                .iter()
                                .find_map(|(inner_field_name, _, inner_field_pat)| {
                                    if inner_field_name.name == field_name {
                                        Some(inner_field_pat.clone())
                                    } else {
                                        None
                                    }
                                })
                                .unwrap()
                        } else {
                            Pattern::Unknown(pat.range())
                        }
                    })
                    .collect::<Vec<_>>();

                // Now, check whether the field patterns differ.
                if let Some(diff) = first_difference(
                    project_index,
                    var.clone()
                        .then(if let Some(variant) = enum_variant.clone() {
                            PlaceSegment::EnumField {
                                variant,
                                field: field_name,
                            }
                        } else {
                            PlaceSegment::DataField { field: field_name }
                        }),
                    field_ty,
                    &field_patterns,
                ) {
                    return Some(diff);
                }
            }

            // The patterns all matched, since we've checked each field and we didn't find a mismatch.
            None
        }
    } else {
        // No patterns are probing inside this variable, so we must assume that they all match.
        None
    }
}

/// Given a list of patterns for a function, in which place do they first (pairwise) differ, and how?
/// If they do not differ, return None. Any `Place` returned will be relative to an argument.
fn first_difference_function(
    project_index: &ProjectIndex,
    arg_types: Vec<Type>,
    patterns: &[Vec<Pattern>],
) -> Option<PatternMismatch> {
    for i in 0..arg_types.len() {
        let arg_patterns = patterns
            .iter()
            .map(|vec| vec[i].clone())
            .collect::<Vec<_>>();
        if let Some(diff) = first_difference(
            project_index,
            Place::new(LocalVariableName::Argument(ArgumentIndex(i as u64))),
            arg_types[i].clone(),
            &arg_patterns,
        ) {
            return Some(diff);
        }
    }
    None
}

/// `arg_patterns` represents some patterns for the arguments of a function.
/// If any of these reference the given place, replace the pattern with the given replacement.
/// This allows us to constrain `_` or named patterns to the known variant
/// after we've switched on the discriminant, so that we don't get infinite recursion.
fn reference_discriminant_function(
    place: Place,
    replacement: Pattern,
    mut arg_patterns: Vec<Pattern>,
) -> Vec<Pattern> {
    let i = if let LocalVariableName::Argument(ArgumentIndex(i)) = place.local {
        i as usize
    } else {
        unreachable!();
    };

    arg_patterns[i] =
        reference_discriminant(place.projection, replacement, arg_patterns[i].clone());
    arg_patterns
}

/// If this pattern references the given place relative to the root of the pattern,
/// replace the pattern with one that matches the given variant.
fn reference_discriminant(
    mut place_segments: Vec<PlaceSegment>,
    replacement: Pattern,
    pattern: Pattern,
) -> Pattern {
    if place_segments.is_empty() {
        // Check if this pattern is "named" or "unknown". If so, replace it with a blank pattern representing this enum variant.
        let should_replace = match pattern {
            Pattern::Named(_) => true,
            Pattern::TypeConstructor { .. } => false,
            Pattern::Function { .. } => unreachable!(),
            Pattern::Unknown(_) => true,
        };

        if should_replace {
            replacement
        } else {
            pattern
        }
    } else {
        let segment = place_segments.remove(0);
        match segment {
            PlaceSegment::DataField { field } => {
                if let Pattern::TypeConstructor {
                    type_ctor,
                    mut fields,
                } = pattern
                {
                    for (field_name, _field_type, field_pat) in &mut fields {
                        if field_name.name == field {
                            *field_pat = reference_discriminant(
                                place_segments,
                                replacement,
                                field_pat.clone(),
                            );
                            break;
                        }
                    }
                    Pattern::TypeConstructor { type_ctor, fields }
                } else {
                    pattern
                }
            }
            PlaceSegment::EnumField { field, .. } => {
                if let Pattern::TypeConstructor {
                    type_ctor,
                    mut fields,
                } = pattern
                {
                    for (field_name, _field_type, field_pat) in &mut fields {
                        if field_name.name == field {
                            *field_pat = reference_discriminant(
                                place_segments,
                                replacement,
                                field_pat.clone(),
                            );
                            break;
                        }
                    }
                    Pattern::TypeConstructor { type_ctor, fields }
                } else {
                    pattern
                }
            }
        }
    }
}

/// Creates a basic block (or tree of basic blocks) that
/// performs the given pattern matching operation for an entire function body.
/// The value is matched against each case, and basic blocks are created that branch to
/// these 'case' blocks when the pattern is matched. The return value is a basic block
/// which will perform this match operation, then jump to the case blocks.
fn perform_match_function(
    project_index: &ProjectIndex,
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    arg_types: Vec<Type>,
    cases: Vec<(Vec<Pattern>, BasicBlockId)>,
) -> BasicBlockId {
    // Recursively find the first difference between patterns, until each case has its own branch.
    let (patterns, blocks): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    if let Some(diff) = first_difference_function(project_index, arg_types.clone(), &patterns) {
        // There was a difference that lets us distinguish some of the patterns into different branches.
        let diff_reason = diff.reason;
        let diff_place = diff.place;
        match diff_reason {
            PatternMismatchReason::EnumDiscriminant { enum_name, cases } => {
                // Create a match operation for each enum discriminant case.
                // If a pattern for a given case does not reference the enum's discriminant, we'll
                // replace it with a dummy pattern that references the discriminant we just matched.
                let cases_matched = cases
                    .into_iter()
                    .map(|(name, cases)| {
                        let new_cases = cases
                            .into_iter()
                            .map(|id| {
                                let enum_fields = if let TypeDeclarationTypeI::Enum(enumi) =
                                    &project_index[&enum_name.source_file].types[&enum_name.name]
                                        .decl_type
                                {
                                    enumi
                                        .variants
                                        .iter()
                                        .find_map(|variant| {
                                            if variant.name.name == name {
                                                Some(
                                                    variant
                                                        .type_ctor
                                                        .fields
                                                        .iter()
                                                        .map(|(name, ty)| {
                                                            (name.name.clone(), ty.clone())
                                                        })
                                                        .collect::<Vec<_>>(),
                                                )
                                            } else {
                                                None
                                            }
                                        })
                                        .unwrap()
                                } else {
                                    unreachable!()
                                };

                                let replacement = Pattern::TypeConstructor {
                                    type_ctor: TypeConstructorInvocation {
                                        data_type: enum_name.clone(),
                                        variant: Some(name.clone()),
                                        // I *think* that num_parameters is not relevant here.
                                        num_parameters: 0,
                                        range,
                                    },
                                    fields: enum_fields
                                        .into_iter()
                                        .map(|(name, ty)| {
                                            let pattern = Pattern::Unknown(range);
                                            (NameP { name, range }, ty, pattern)
                                        })
                                        .collect(),
                                };

                                (
                                    reference_discriminant_function(
                                        diff_place.clone(),
                                        replacement,
                                        patterns[id].clone(),
                                    ),
                                    blocks[id],
                                )
                            })
                            .collect();
                        (
                            name,
                            perform_match_function(
                                project_index,
                                ctx,
                                range,
                                arg_types.clone(),
                                new_cases,
                            ),
                        )
                    })
                    .collect::<HashMap<_, _>>();

                // Now, each case has been successfully pattern matched to its entirety.
                // Finally, construct the switch statement to switch between the given cases.
                ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: Vec::new(),
                    terminator: Terminator {
                        range,
                        kind: TerminatorKind::SwitchDiscriminator {
                            enum_name,
                            enum_place: diff_place,
                            cases: cases_matched,
                        },
                    },
                })
            }
        }
    } else {
        // There was no difference between the patterns.
        // The first case listed is the "correct" one, since we match earlier cases first.
        blocks[0]
    }
}

/// Chains a series of basic blocks together, assuming that they do not have terminators.
/// Returns a single basic block that has an invalid terminator.
fn chain(
    ctx: &mut DefinitionTranslationContext,
    blocks: Vec<BasicBlockId>,
    range: Range,
) -> BasicBlockId {
    let blocks = blocks
        .into_iter()
        .map(|block_id| {
            ctx.control_flow_graph
                .basic_blocks
                .remove(&block_id)
                .unwrap()
        })
        .collect::<Vec<_>>();

    ctx.control_flow_graph.new_basic_block(BasicBlock {
        statements: blocks
            .into_iter()
            .map(|block| {
                assert!(matches!(block.terminator.kind, TerminatorKind::Invalid));
                block.statements
            })
            .flatten()
            .collect(),
        terminator: Terminator {
            range,
            kind: TerminatorKind::Invalid,
        },
    })
}

struct ChainGeneratedM {
    /// The basic block that will, once called, compute the values in this chain, and store it in the given local variables.
    block: BasicBlockId,
    /// The targets that will have the chain's results stored into them.
    variables: Vec<LocalVariableName>,
    /// Some expressions require temporary variables to be kept alive until the end of a statement.
    /// By adding values to this list, the given local variables will be dropped after the surrounding statement (or expression) ends.
    /// In particular, the drop occurs at the next semicolon, or if there is not one, the end of the definition as a whole.
    locals_to_drop: Vec<LocalVariableName>,
}

/// Generates a chain of expressions, with the given terminator.
/// Returns the basic block that can be invoked in order to invoke the chain, along ith the variables
/// produced by each expression.
fn generate_chain_with_terminator(
    ctx: &mut DefinitionTranslationContext,
    exprs: Vec<Expression>,
    mut terminator: Terminator,
) -> ChainGeneratedM {
    let range = terminator.range;

    let mut first_block = None;
    let mut locals = Vec::new();
    let mut locals_to_drop = Vec::new();

    for expr in exprs.into_iter().rev() {
        let gen = generate_expr(ctx, expr, terminator);
        locals.insert(0, gen.variable);
        terminator = Terminator {
            range,
            kind: TerminatorKind::Goto(gen.block),
        };
        first_block = Some(gen.block);
        locals_to_drop.extend(gen.locals_to_drop);
    }

    let first_block = first_block.unwrap_or_else(|| {
        ctx.control_flow_graph.new_basic_block(BasicBlock {
            statements: Vec::new(),
            terminator,
        })
    });

    ChainGeneratedM {
        block: first_block,
        variables: locals,
        locals_to_drop,
    }
}

/// Creates a local variable for each bound variable in a pattern, assuming that the given value
/// has the given pattern, and the given type.
/// Returns a basic block that initialises these variables, and that terminates with the given terminator.
/// If no variables need to be initialised, returns None.
fn bind_pattern_variables(
    ctx: &mut DefinitionTranslationContext,
    value: Place,
    pat: &Pattern,
    ty: Type,
) -> Option<BasicBlockId> {
    match pat {
        Pattern::Named(name) => {
            let var = ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty,
                name: Some(name.name.clone()),
            });

            // Initialise this local variable with the supplied value.
            let assign = Statement {
                range: name.range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(var),
                    source: Rvalue::Use(Operand::Move(value)),
                },
            };

            Some(ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![assign],
                terminator: Terminator {
                    range: name.range,
                    kind: TerminatorKind::Invalid,
                },
            }))
        }
        Pattern::TypeConstructor { type_ctor, fields } => {
            // Bind each field individually, then chain all the blocks together.
            let blocks = fields
                .iter()
                .filter_map(|(field_name, ty, pat)| {
                    bind_pattern_variables(
                        ctx,
                        value
                            .clone()
                            .then(if let Some(variant) = type_ctor.variant.clone() {
                                PlaceSegment::EnumField {
                                    variant,
                                    field: field_name.name.clone(),
                                }
                            } else {
                                PlaceSegment::DataField {
                                    field: field_name.name.clone(),
                                }
                            }),
                        pat,
                        ty.clone(),
                    )
                })
                .collect::<Vec<_>>();
            if blocks.is_empty() {
                None
            } else {
                Some(chain(ctx, blocks, type_ctor.range))
            }
        }
        Pattern::Function { .. } => {
            unreachable!("functions are forbidden in arg patterns")
        }
        Pattern::Unknown(_) => None,
    }
}

/// Sets up the context for dealing with this expression.
fn initialise_expr(ctx: &mut DefinitionTranslationContext, expr: &Expression) {
    match &expr.contents {
        ExpressionContentsGeneric::Argument(_) => {}
        ExpressionContentsGeneric::Local(_) => {}
        ExpressionContentsGeneric::Symbol { .. } => {}
        ExpressionContentsGeneric::Apply(left, right) => {
            initialise_expr(ctx, &left);
            initialise_expr(ctx, &right);
        }
        ExpressionContentsGeneric::Lambda { .. } => {}
        ExpressionContentsGeneric::Let { name, expr, .. } => {
            ctx.new_local_variable(LocalVariableInfo {
                range: name.range,
                ty: expr.ty.clone(),
                name: Some(name.name.clone()),
            });
        }
        ExpressionContentsGeneric::Block { statements, .. } => {
            for stmt in statements {
                initialise_expr(ctx, stmt);
            }
        }
        ExpressionContentsGeneric::ConstructData { fields, .. } => {
            for (_, expr) in fields {
                initialise_expr(ctx, expr);
            }
        }
        ExpressionContentsGeneric::ImmediateValue { .. } => {}
    }
}

struct ExprGeneratedM {
    /// The basic block that will, once called, compute the value of this expression, and store it in the given local variable.
    block: BasicBlockId,
    /// The target that will have the expression's result stored into it.
    variable: LocalVariableName,
    /// Some expressions require temporary variables to be kept alive until the end of a statement.
    /// By adding values to this list, the given local variables will be dropped after the surrounding statement (or expression) ends.
    /// In particular, the drop occurs at the next semicolon, or if there is not one, the end of the definition as a whole.
    locals_to_drop: Vec<LocalVariableName>,
}

/// Generates a basic block that computes the value of this expression, and stores the result in the given local.
/// The block generated will have the given terminator.
fn generate_expr(
    ctx: &mut DefinitionTranslationContext,
    expr: Expression,
    terminator: Terminator,
) -> ExprGeneratedM {
    let range = expr.range();
    let ty = expr.ty;
    match expr.contents {
        ExpressionContentsGeneric::Argument(arg) => {
            // Create an empty basic block.
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let variable = ctx.get_name_of_local(&arg.name);
            ExprGeneratedM {
                block,
                variable,
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Local(local) => {
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let variable = ctx.get_name_of_local(&local.name);
            ExprGeneratedM {
                block,
                variable,
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Symbol {
            name,
            range,
            type_variables,
        } => {
            // Instantiate the given symbol.
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![Statement {
                    range,
                    kind: StatementKind::InstanceSymbol {
                        name,
                        type_variables,
                        target: LocalVariableName::Local(variable),
                    },
                }],
                terminator,
            });
            ExprGeneratedM {
                block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Apply(left, right) => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });

            let (argument_type, return_type) = if let Type::Function(l, r) = left.ty.clone() {
                (*l, *r)
            } else {
                unreachable!()
            };

            let right = generate_expr(
                ctx,
                *right,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );
            let left = generate_expr(
                ctx,
                *left,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(right.block),
                },
            );

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements
                .push(Statement {
                    range,
                    kind: StatementKind::Apply {
                        argument: Rvalue::Use(Operand::Move(Place::new(right.variable))),
                        function: Rvalue::Use(Operand::Move(Place::new(left.variable))),
                        target: LocalVariableName::Local(variable),
                        return_type,
                        argument_type,
                    },
                });

            ExprGeneratedM {
                block: left.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: left
                    .locals_to_drop
                    .into_iter()
                    .chain(right.locals_to_drop)
                    .collect(),
            }
        }
        ExpressionContentsGeneric::Lambda {
            params,
            expr: substituted_expr,
            ..
        } => {
            // Create the given lambda.
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: ty.clone(),
                name: None,
            });
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![Statement {
                    range,
                    kind: StatementKind::CreateLambda {
                        ty,
                        params,
                        //expr: substituted_expr,
                        target: LocalVariableName::Local(variable),
                    },
                }],
                terminator,
            });
            ExprGeneratedM {
                block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
        ExpressionContentsGeneric::Let {
            name,
            expr: right_expr,
            ..
        } => {
            // Let expressions return the unit value.
            let ret = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: Type::Primitive(PrimitiveType::Unit),
                name: None,
            });

            // Let expressions are handled in two phases. First, (before calling this function)
            // we initialise the context with a blank variable of the right name and type, so that
            // other expressions can access it. Then, we assign a value to the variable in this function now.
            let variable = ctx.get_name_of_local(&name.name);
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });

            // Create the RHS of the let expression, and assign it to the LHS.
            let mut rvalue = generate_expr(
                ctx,
                *right_expr,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );

            let statements = &mut ctx
                .control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements;

            statements.push(Statement {
                range,
                kind: StatementKind::Assign {
                    target: variable,
                    source: Rvalue::Use(Operand::Move(Place::new(rvalue.variable))),
                },
            });
            statements.push(Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(ret),
                    source: Rvalue::Use(Operand::Constant(ImmediateValue::Unit)),
                },
            });

            rvalue.locals_to_drop.push(variable);

            ExprGeneratedM {
                block: rvalue.block,
                variable: LocalVariableName::Local(ret),
                locals_to_drop: rvalue.locals_to_drop,
            }
        }
        ExpressionContentsGeneric::Block {
            mut statements,
            final_semicolon,
            ..
        } => {
            // Make a list of all the local variables we'll need to drop at the end of this scope.
            let locals_to_drop = statements
                .iter()
                .filter_map(|expr| {
                    if let ExpressionContentsGeneric::Let { name, .. } = &expr.contents {
                        Some(name.name.clone())
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>();

            // Make a basic block that drops these variables, in reverse order.
            let drop_block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: locals_to_drop
                    .iter()
                    .rev()
                    .map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive {
                            variable: ctx.get_name_of_local(local),
                        },
                    })
                    .collect(),
                terminator,
            });
            let drop_terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(drop_block),
            };

            let final_expression = if final_semicolon.is_none() {
                statements.pop()
            } else {
                None
            };

            if let Some(final_expression) = final_expression {
                let final_expr = generate_expr(ctx, final_expression, drop_terminator);

                let mut chain = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(final_expr.block),
                    },
                );
                chain.locals_to_drop.extend(chain.variables);
                ctx.control_flow_graph
                    .basic_blocks
                    .get_mut(&drop_block)
                    .unwrap()
                    .statements
                    .extend(chain.locals_to_drop.into_iter().map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive { variable: local },
                    }));

                ExprGeneratedM {
                    block: chain.block,
                    variable: final_expr.variable,
                    locals_to_drop: Vec::new(),
                }
            } else {
                // We need to make a new unit variable since there was no final expression.
                // This is the variable that is returned by the block.
                let variable = ctx.new_local_variable(LocalVariableInfo {
                    range,
                    ty: Type::Primitive(PrimitiveType::Unit),
                    name: None,
                });

                // Initialise the variable with an empty value.
                let assign = Statement {
                    range,
                    kind: StatementKind::Assign {
                        target: LocalVariableName::Local(variable),
                        source: Rvalue::Use(Operand::Constant(ImmediateValue::Unit)),
                    },
                };

                let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: vec![assign],
                    terminator: drop_terminator,
                });

                let mut chain = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(initialise_variable),
                    },
                );
                chain.locals_to_drop.extend(chain.variables);
                ctx.control_flow_graph
                    .basic_blocks
                    .get_mut(&drop_block)
                    .unwrap()
                    .statements
                    .extend(chain.locals_to_drop.into_iter().map(|local| Statement {
                        range,
                        kind: StatementKind::DropIfAlive { variable: local },
                    }));

                ExprGeneratedM {
                    block: chain.block,
                    variable: LocalVariableName::Local(variable),
                    locals_to_drop: Vec::new(),
                }
            }
        }
        ExpressionContentsGeneric::ConstructData {
            fields, variant, ..
        } => {
            // Break each field into its name and its expression.
            let (names, expressions): (Vec<_>, Vec<_>) = fields.into_iter().unzip();

            // Now, construct the data.
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty: ty.clone(),
                name: None,
            });

            // Create a block to initialise the variable with its new value.
            let construct_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![],
                terminator,
            });

            // Chain the construction of the fields.
            let chain = generate_chain_with_terminator(
                ctx,
                expressions,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(construct_variable),
                },
            );

            // Now, after we've constructed the fields, make the new variable with them.
            let construct = Statement {
                range,
                kind: StatementKind::ConstructData {
                    ty,
                    variant,
                    fields: chain
                        .variables
                        .into_iter()
                        .zip(names)
                        .map(|(name, field_name)| {
                            (
                                field_name.name,
                                Rvalue::Use(Operand::Move(Place::new(name))),
                            )
                        })
                        .collect(),
                    target: LocalVariableName::Local(variable),
                },
            };
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&construct_variable)
                .unwrap()
                .statements
                .push(construct);

            // Finally, chain the construction of the new variable with its fields.

            ExprGeneratedM {
                block: chain.block,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: chain.locals_to_drop,
            }
        }
        ExpressionContentsGeneric::ImmediateValue { value, range } => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

            // Initialise the variable with an empty value.
            let assign = Statement {
                range,
                kind: StatementKind::Assign {
                    target: LocalVariableName::Local(variable),
                    source: Rvalue::Use(Operand::Constant(value)),
                },
            };

            let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![assign],
                terminator,
            });

            ExprGeneratedM {
                block: initialise_variable,
                variable: LocalVariableName::Local(variable),
                locals_to_drop: Vec::new(),
            }
        }
    }
}
