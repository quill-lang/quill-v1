//! Definitions for all of the MIR constructs.

use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt::Display,
};

use quill_common::{
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_index::TypeParameter;
use quill_parser::expr_pat::ConstantValue;
use quill_type::Type;

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct ArgumentIndex(pub u64);
impl Display for ArgumentIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}arg", self.0)
    }
}
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy, PartialOrd, Ord)]
pub struct LocalVariableId(pub u64);
impl Display for LocalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}local", self.0)
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
    pub body: DefinitionBodyM,
}

impl Ranged for DefinitionM {
    fn range(&self) -> Range {
        self.range
    }
}

impl Display for DefinitionM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "arity: {}", self.arity)?;
        for (var, info) in &self.local_variable_names {
            writeln!(f, "    {} >> let {}: {}", info.range, var, info)?;
        }
        writeln!(f, "{}", self.body)
    }
}

#[derive(Debug, Clone)]
pub enum DefinitionBodyM {
    PatternMatch(ControlFlowGraph),
    CompilerIntrinsic,
}

impl Display for DefinitionBodyM {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DefinitionBodyM::PatternMatch(cfg) => {
                writeln!(f, "{}", cfg)
            }
            DefinitionBodyM::CompilerIntrinsic => {
                writeln!(f, "compiler intrinsic")
            }
        }
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
            LocalVariableName::Argument(arg) => write!(f, "{}", arg),
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
    /// Which basic block should be entered to invoke the function?
    pub entry_point: BasicBlockId,
}

impl ControlFlowGraph {
    /// Creates a new control flow graph with entry point 0 and no basic blocks.
    pub(crate) fn new() -> Self {
        Self {
            next_block_id: BasicBlockId(0),
            entry_point: BasicBlockId(0),
            basic_blocks: BTreeMap::new(),
        }
    }
}

impl Display for ControlFlowGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "entry point: {}", self.entry_point)?;

        for (block_id, block) in &self.basic_blocks {
            writeln!(f, "{}:", block_id)?;
            for stmt in &block.statements {
                writeln!(f, "    {}", stmt)?;
            }
            writeln!(f, "    {}", block.terminator)?;
        }

        Ok(())
    }
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
    pub(crate) fn reorder(&mut self) {
        // We use a topological sort (Kahn's algorithm) to reorder basic blocks.

        // Cache some things about each block.
        // In particular, we need to know which other blocks a block can end up jumping to.
        let mut target_blocks = HashMap::new();
        for (&node, block) in &self.basic_blocks {
            let mut block_target_blocks = HashSet::new();
            // First, check possible places we'll jump to in the terminator.
            match &block.terminator.kind {
                TerminatorKind::Goto(target) => {
                    block_target_blocks.insert(*target);
                }
                TerminatorKind::SwitchDiscriminant { cases, .. } => {
                    for target in cases.values() {
                        block_target_blocks.insert(*target);
                    }
                }
                TerminatorKind::SwitchConstant { cases, default, .. } => {
                    for target in cases.values() {
                        block_target_blocks.insert(*target);
                    }
                    block_target_blocks.insert(*default);
                }
                TerminatorKind::Invalid => unreachable!(),
                TerminatorKind::Return { .. } => {}
            }
            target_blocks.insert(node, block_target_blocks);
        }

        // Now that we have all this information, we can make a set of all the edges in this directed graph.
        let mut edges = HashMap::new();
        for &node in self.basic_blocks.keys() {
            edges.insert(
                node,
                target_blocks[&node].iter().copied().collect::<Vec<_>>(),
            );
        }

        // Now run Kahn's algorithm.
        // The set of start nodes is exactly the entry point of the function.
        let mut l = Vec::new();
        let mut s = vec![self.entry_point];
        while let Some(node) = s.pop() {
            l.push(node);
            // Look for each node that follows from this block.
            for following in edges.remove(&node).into_iter().flatten() {
                // Check to see if there are any other incoming edges into this following node.
                if !edges.values().flatten().any(|id| *id == following) {
                    s.push(following);
                }
            }
        }

        // If this assert fails, then some blocks in the CFG are never reached from the entry point.
        // This could happen if the MIR generation does not correctly represent the HIR's control flow.
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
                    *target = block_id_map[target];
                }
                TerminatorKind::SwitchDiscriminant { cases, .. } => {
                    for target in cases.values_mut() {
                        *target = block_id_map[target];
                    }
                }
                TerminatorKind::SwitchConstant { cases, default, .. } => {
                    for target in cases.values_mut() {
                        *target = block_id_map[target];
                    }
                    *default = block_id_map[default];
                }
                TerminatorKind::Invalid => unreachable!(),
                TerminatorKind::Return { .. } => {}
            }
        }

        self.entry_point = block_id_map[&self.entry_point];
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
        argument: Box<Rvalue>,
        function: Box<Rvalue>,
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
    /// Creates an object of a given type, and puts it in target.
    ConstructData {
        ty: Type,
        /// If this type was an enum, which variant should we create?
        variant: Option<String>,
        fields: HashMap<String, Rvalue>,
        target: LocalVariableName,
    },
    /// Creates an impl of an aspect from a set of definitions.
    /// The definitions are instanced symbols.
    /// They are considered to be "moved into" the impl for ownership purposes.
    ConstructImpl {
        aspect: QualifiedName,
        type_variables: Vec<Type>,
        definitions: HashMap<String, LocalVariableName>,
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
            StatementKind::ConstructImpl {
                aspect,
                type_variables,
                definitions,
                target,
            } => {
                write!(f, "{} = impl {}", target, aspect)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty_var in type_variables {
                        write!(f, " {}", ty_var)?;
                    }
                }
                if !definitions.is_empty() {
                    write!(f, " using ")?;
                    for (i, (def_name, def_local)) in definitions.iter().enumerate() {
                        if i != 0 {
                            write!(f, "; ")?;
                        }
                        write!(f, "{} = {}", def_name, def_local)?;
                    }
                }
                Ok(())
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
    EnumDiscriminant,
    ImplField { field: String },
}

impl Display for PlaceSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceSegment::DataField { field } => write!(f, ".{}", field),
            PlaceSegment::EnumField { variant, field } => write!(f, ".<{}>.{}", variant, field),
            PlaceSegment::EnumDiscriminant => write!(f, ".discriminant"),
            PlaceSegment::ImplField { field } => write!(f, ".<impl>.{}", field),
        }
    }
}

/// Represents the use of a value that we can feed into an expression or function.
/// We can only read from (not write to) an rvalue.
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// Either a copy or a move, depending on the type.
    Use(Operand),
    /// Creates a borrow of a local variable.
    /// Borrowing more complicated things is only an emergent behaviour created by functions.
    /// The borrow's lifetime will be managed later in the borrow checker.
    Borrow(LocalVariableName),
}

impl Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rvalue::Use(operand) => write!(f, "use {}", operand),
            Rvalue::Borrow(place) => write!(f, "borrow {}", place),
        }
    }
}

/// A value that we can read from.
#[derive(Debug, Clone)]
pub enum Operand {
    /// We will copy data from this place without dropping it.
    Copy(Place),
    /// We will move data out of this place, possibly dropping and freeing it.
    Move(Place),
    /// Generates a new constant value.
    Constant(ConstantValue),
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
    SwitchDiscriminant {
        /// What enum are we switching on?
        enum_name: QualifiedName,
        /// What type parameters did this enum have?
        enum_parameters: Vec<Type>,
        /// Where is this enum stored?
        enum_place: Place,
        /// Maps the names of enum discriminants to the basic block ID to jump to.
        /// This map must exhaustively cover every possible enum discriminant.
        cases: HashMap<String, BasicBlockId>,
    },
    /// Works out which value a given local variable has.
    SwitchConstant {
        /// Where is this value stored?
        place: Place,
        /// Maps the names of constant values to the basic block ID to jump to.
        /// If the constant is a boolean, this must be exhaustive. Otherwise,
        /// there should be a default case to cover missed possibilities.
        cases: HashMap<ConstantValue, BasicBlockId>,
        default: BasicBlockId,
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
            TerminatorKind::SwitchDiscriminant {
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
            TerminatorKind::SwitchConstant {
                place,
                cases,
                default,
            } => {
                write!(f, "switch {} {{", place)?;
                for (case, id) in cases {
                    write!(f, " {} -> {},", case, id)?;
                }
                write!(f, " default {}", default)?;
                write!(f, " }}")
            }
            TerminatorKind::Invalid => write!(f, "invalid"),
            TerminatorKind::Return { value } => write!(f, "return {}", value),
        }
    }
}
