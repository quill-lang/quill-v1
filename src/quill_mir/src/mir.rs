//! Definitions for all of the MIR constructs.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::Display,
};

use quill_common::{
    location::{Location, Range, Ranged},
    name::QualifiedName,
};
use quill_index::TypeParameter;
use quill_parser::expr_pat::ConstantValue;
use quill_type::Type;

use crate::validate::type_of_value;

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct ArgumentIndex(pub u64);
impl Display for ArgumentIndex {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}arg", self.0)
    }
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub struct LocalVariableId(pub u64);
impl Display for LocalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}local", self.0)
    }
}
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
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
        write!(f, "type variables:")?;
        for type_variable in &self.type_variables {
            write!(f, " {}", type_variable)?;
        }
        writeln!(f)?;
        for (var, info) in &self.local_variable_names {
            writeln!(f, "    {} >> let {}: {}", info.range, var, info)?;
        }
        writeln!(f, "{}", self.body)
    }
}

// Since pretty much the whole point of the enum is the CFG, the size difference is irrelevant here.
#[allow(clippy::large_enum_variant)]
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

impl DefinitionM {
    /// Generates the type of this definition as a whole.
    /// This essentially erases arity information.
    pub fn symbol_type(&self) -> Type {
        let mut ty = self.return_type.clone();
        for i in (0..self.arity).rev() {
            let arg_ty = self.local_variable_names[&LocalVariableName::Argument(ArgumentIndex(i))]
                .ty
                .clone();
            ty = Type::Function(Box::new(arg_ty), Box::new(ty));
        }
        ty
    }
}

/// A local variable is a value which can be operated on by functions and expressions.
/// Other objects, such as symbols in global scope, must be instanced as local variables
/// before being operated on. This allows the borrow checker and the code translator
/// to better understand the control flow and data flow.
#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
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
    /// Do we know any information about this local variable from static analysis?
    pub details: LocalVariableDetails,
}

impl Display for LocalVariableInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.ty)?;
        write!(f, "\n{}", self.details)?;
        Ok(())
    }
}

#[derive(Debug, Default, Clone)]
pub struct LocalVariableDetails {
    /// If this variable had a name, what was it?
    pub name: Option<String>,
    /// Do we know the value of the local variable statically?
    pub value: Option<KnownValue>,
}

impl Display for LocalVariableDetails {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(name) = &self.name {
            writeln!(f, "    name = {}", name)?;
        }
        if let Some(value) = &self.value {
            writeln!(
                f,
                "    value = {}",
                value.to_string().replace("\n", "\n        ")
            )?;
        }
        Ok(())
    }
}

/// A value that we know at compile time.
/// Useful for inlining.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum KnownValue {
    Constant(ConstantValue),
    Instantiate {
        name: QualifiedName,
        type_variables: Vec<Type>,
        /// In certain cases, we may already know the value of some initial arguments
        /// (typically impls). These are stored here.
        special_case_arguments: Vec<KnownValue>,
    },
    ConstructData {
        name: QualifiedName,
        type_variables: Vec<Type>,
        /// If this type was an enum, which variant should we create?
        variant: Option<String>,
        fields: BTreeMap<String, KnownValue>,
    },
    ConstructImpl {
        aspect: QualifiedName,
        type_variables: Vec<Type>,
        definitions: BTreeMap<String, KnownValue>,
    },
}

impl Display for KnownValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KnownValue::Constant(constant) => {
                write!(f, "const {}", constant)
            }
            KnownValue::Instantiate {
                name,
                type_variables,
                special_case_arguments,
            } => {
                write!(f, "instantiate {}", name)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty in type_variables {
                        write!(f, " {}", ty)?;
                    }
                }
                if !special_case_arguments.is_empty() {
                    writeln!(f, " special case")?;
                    for arg in special_case_arguments {
                        write!(f, "{}", arg.to_string().replace("\n", "\n    "))?;
                    }
                }
                Ok(())
            }
            KnownValue::ConstructData {
                name,
                type_variables,
                variant,
                fields,
            } => {
                write!(f, "construct {}", name)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty in type_variables {
                        write!(f, " {}", ty)?;
                    }
                }
                if let Some(variant) = variant {
                    write!(f, " variant {}", variant)?;
                }
                for (field_name, value) in fields {
                    writeln!(f)?;
                    let value_str = value.to_string().replace("\n", "\n    ");
                    write!(f, "{} = {}", field_name, value_str)?;
                }
                Ok(())
            }
            KnownValue::ConstructImpl {
                aspect,
                type_variables,
                definitions,
            } => {
                write!(f, "construct impl {}", aspect)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty in type_variables {
                        write!(f, " {}", ty)?;
                    }
                }
                for (field_name, value) in definitions {
                    writeln!(f)?;
                    let value_str = value.to_string().replace("\n", "\n    ");
                    write!(f, "{} = {}", field_name, value_str)?;
                }
                Ok(())
            }
        }
    }
}

impl KnownValue {
    /// A display impl for creating a function signature, not for displaying in MIR.
    pub fn display_in_mono(&self) -> String {
        match self {
            KnownValue::Constant(value) => value.to_string(),
            KnownValue::Instantiate {
                name,
                type_variables,
                special_case_arguments,
            } => {
                let mut result = name.to_string();
                for ty in type_variables {
                    result += "[";
                    result += &ty.to_string();
                    result += "]";
                }
                for arg in special_case_arguments {
                    result += "(";
                    result += &arg.to_string();
                    result += ")";
                }
                result
            }
            KnownValue::ConstructData {
                name,
                type_variables,
                variant,
                fields,
            } => {
                let mut result = name.to_string();
                if let Some(variant) = variant {
                    result += "~";
                    result += variant;
                }
                for ty in type_variables {
                    result += "[";
                    result += &ty.to_string();
                    result += "]";
                }
                for (field_name, value) in fields {
                    result += &format!("({}={})", field_name, value);
                }
                result
            }
            KnownValue::ConstructImpl {
                aspect,
                type_variables,
                definitions,
            } => {
                let mut result = "impl ".to_string() + &aspect.to_string();
                for ty in type_variables {
                    result += "[";
                    result += &ty.to_string();
                    result += "]";
                }
                for (field_name, value) in definitions {
                    result += &format!("({}={})", field_name, value);
                }
                result
            }
        }
    }

    /// Generate MIR instructions to construct this known value.
    /// We are allowed to create new local variables with IDs greater than or equal to next_local_id.
    /// This function will also create a new entry in locals for the new variable.
    pub fn generate(
        &self,
        target: LocalVariableName,
        mut next_local_id: u64,
        locals: &mut BTreeMap<LocalVariableName, LocalVariableInfo>,
        definition_infos: impl Clone + Fn(&QualifiedName, &[Type], &[KnownValue]) -> DefinitionInfo,
    ) -> GenerationResult {
        let range = Location { line: 0, col: 0 }.into();
        match self {
            KnownValue::Constant(value) => {
                locals.insert(
                    target,
                    LocalVariableInfo {
                        range,
                        ty: Type::Primitive(type_of_value(*value)),
                        details: Default::default(),
                    },
                );
                GenerationResult {
                    statements: vec![Statement {
                        range,
                        kind: StatementKind::Assign {
                            target,
                            source: Rvalue::Constant(*value),
                        },
                    }],
                    next_local_id,
                }
            }
            KnownValue::Instantiate {
                name,
                type_variables,
                special_case_arguments,
            } => {
                let mir_def = definition_infos(name, type_variables, special_case_arguments);
                locals.insert(
                    target,
                    LocalVariableInfo {
                        range,
                        // Since the mir_def is a special case function, we do not actually pass the special case arguments in manually.
                        // This means the symbol type doesn't need to be changed depending on `special_case_arguments.len()`.
                        ty: mir_def.symbol_type,
                        details: Default::default(),
                    },
                );
                GenerationResult {
                    statements: vec![Statement {
                        range,
                        kind: StatementKind::InstanceSymbol {
                            name: name.clone(),
                            type_variables: type_variables.clone(),
                            special_case_arguments: special_case_arguments.clone(),
                            target,
                        },
                    }],
                    next_local_id,
                }
            }
            KnownValue::ConstructData {
                name,
                type_variables,
                variant,
                fields,
            } => {
                let mut statements = Vec::new();
                let mut field_entries = BTreeMap::new();
                for (field_name, field_value) in fields {
                    let field_local = LocalVariableName::Local(LocalVariableId(next_local_id));
                    next_local_id += 1;
                    let inner_result = field_value.generate(
                        field_local,
                        next_local_id,
                        locals,
                        definition_infos.clone(),
                    );
                    next_local_id = inner_result.next_local_id;
                    statements.extend(inner_result.statements);
                    field_entries.insert(field_name.clone(), Rvalue::Move(Place::new(field_local)));
                }
                statements.push(Statement {
                    range,
                    kind: StatementKind::ConstructData {
                        name: name.clone(),
                        type_variables: type_variables.clone(),
                        variant: variant.clone(),
                        fields: field_entries,
                        target,
                    },
                });
                locals.insert(
                    target,
                    LocalVariableInfo {
                        range,
                        ty: Type::Named {
                            name: name.clone(),
                            parameters: type_variables.clone(),
                        },
                        details: Default::default(),
                    },
                );
                GenerationResult {
                    statements,
                    next_local_id,
                }
            }
            KnownValue::ConstructImpl {
                aspect,
                type_variables,
                definitions,
            } => {
                let mut statements = Vec::new();
                let mut field_entries = BTreeMap::new();
                for (field_name, field_value) in definitions {
                    let field_local = LocalVariableName::Local(LocalVariableId(next_local_id));
                    next_local_id += 1;
                    let inner_result = field_value.generate(
                        field_local,
                        next_local_id,
                        locals,
                        definition_infos.clone(),
                    );
                    next_local_id = inner_result.next_local_id;
                    statements.extend(inner_result.statements);
                    field_entries.insert(field_name.clone(), field_local);
                }
                statements.push(Statement {
                    range,
                    kind: StatementKind::ConstructImpl {
                        aspect: aspect.clone(),
                        type_variables: type_variables.clone(),
                        definitions: field_entries,
                        target,
                    },
                });
                locals.insert(
                    target,
                    LocalVariableInfo {
                        range,
                        ty: Type::Impl {
                            name: aspect.clone(),
                            parameters: type_variables.clone(),
                        },
                        details: Default::default(),
                    },
                );
                GenerationResult {
                    statements,
                    next_local_id,
                }
            }
        }
    }
}

#[derive(Clone)]
pub struct DefinitionInfo {
    // TODO: use arity information to avoid adding an amount of special case arguments exceeding the function's arity
    pub arity: u64,
    pub symbol_type: Type,
}

pub struct GenerationResult {
    pub statements: Vec<Statement>,
    pub next_local_id: u64,
}

/// After validation, the control flow graph must be in a topologically sorted order:
/// we jump only from lower-indexed basic blocks to higher-indexed basic blocks.
/// This means that, to trace control flow, ensuring that each variable is initialised before used,
/// you can just iterate in order over the list of basic blocks.
#[derive(Debug, Clone)]
pub struct ControlFlowGraph {
    next_block_id: BasicBlockId,
    /// Every basic block has a unique index, which is its index inside this basic blocks map.
    /// When jumping between basic blocks, we must provide the index of the target block.
    pub basic_blocks: BTreeMap<BasicBlockId, BasicBlock>,
    /// Which basic block should be entered to invoke the function?
    pub entry_point: BasicBlockId,
    /// If we know the return value statically, it is given here.
    pub return_value: Option<KnownValue>,
}

impl ControlFlowGraph {
    /// Creates a new control flow graph with entry point 0 and no basic blocks.
    pub(crate) fn new() -> Self {
        Self {
            next_block_id: BasicBlockId(0),
            entry_point: BasicBlockId(0),
            basic_blocks: BTreeMap::new(),
            return_value: None,
        }
    }
}

impl Display for ControlFlowGraph {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(val) = &self.return_value {
            writeln!(f, "returns {}", val.to_string().replace("\n", "\n    "))?;
        }
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
        let mut target_blocks = BTreeMap::new();
        for (&node, block) in &self.basic_blocks {
            let mut block_target_blocks = BTreeSet::new();
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
        let mut edges = BTreeMap::new();
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
        assert!(edges.is_empty(), "edges: {:?}\ncfg: {}", edges, self);

        // Now, reorder the basic block IDs according to this new order in `l`.
        // This map maps from old block IDs to new block IDs.
        let block_id_map = l
            .into_iter()
            .enumerate()
            .map(|(new_id, old_id)| (old_id, BasicBlockId(new_id as u64)))
            .collect::<BTreeMap<_, _>>();

        // First we'll move them around in the CFG then we'll update all references to these IDs inside terminators.
        for (old_id, block) in std::mem::take(&mut self.basic_blocks) {
            self.basic_blocks.insert(block_id_map[&old_id], block);
        }
        // Now update all the references.
        for block in self.basic_blocks.values_mut() {
            for stmt in &mut block.statements {
                if let StatementKind::AssignPhi { phi_cases, .. } = &mut stmt.kind {
                    for (source, _) in phi_cases.iter_mut() {
                        *source = block_id_map[source];
                    }
                }
            }
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

    /// Replaces the uses of the given variable with the replacement.
    pub fn replace_uses(&mut self, original: LocalVariableName, replacement: LocalVariableName) {
        let replace_local = |local: &mut LocalVariableName| {
            if *local == original {
                *local = replacement;
            }
        };
        let replace_place = |place: &mut Place| replace_local(&mut place.local);
        let replace_rvalue = |rvalue: &mut Rvalue| match rvalue {
            Rvalue::Move(place) => replace_place(place),
            Rvalue::Borrow(local) | Rvalue::Copy(local) => replace_local(local),
            Rvalue::Constant(_) => {}
        };

        for block in self.basic_blocks.values_mut() {
            for stmt in &mut block.statements {
                match &mut stmt.kind {
                    StatementKind::Assign { target, source } => {
                        replace_local(target);
                        replace_rvalue(source)
                    }
                    StatementKind::AssignPhi { target, phi_cases } => {
                        replace_local(target);
                        for (_block, source) in phi_cases.iter_mut() {
                            replace_local(source);
                        }
                    }
                    StatementKind::InstanceSymbol { target, .. } => {
                        replace_local(target);
                    }
                    StatementKind::Apply {
                        argument,
                        function,
                        target,
                    } => {
                        replace_rvalue(argument);
                        replace_rvalue(function);
                        replace_local(target);
                    }
                    StatementKind::InvokeFunction {
                        target, arguments, ..
                    } => {
                        replace_local(target);
                        for arg in arguments {
                            replace_rvalue(arg);
                        }
                    }
                    StatementKind::ConstructFunctionObject {
                        target,
                        curried_arguments,
                        ..
                    } => {
                        replace_local(target);
                        for arg in curried_arguments {
                            replace_rvalue(arg);
                        }
                    }
                    StatementKind::InvokeFunctionObject {
                        func_object,
                        target,
                        additional_arguments,
                    } => {
                        replace_rvalue(func_object);
                        replace_local(target);
                        for arg in additional_arguments {
                            replace_rvalue(arg);
                        }
                    }
                    StatementKind::Drop { variable } => {
                        replace_local(variable);
                    }
                    StatementKind::Free { variable } => {
                        replace_local(variable);
                    }
                    StatementKind::ConstructData { fields, target, .. } => {
                        for rvalue in fields.values_mut() {
                            replace_rvalue(rvalue);
                        }
                        replace_local(target);
                    }
                    StatementKind::ConstructImpl {
                        definitions,
                        target,
                        ..
                    } => {
                        for value in definitions.values_mut() {
                            replace_local(value);
                        }
                        replace_local(target);
                    }
                }
            }

            match &mut block.terminator.kind {
                TerminatorKind::Goto(_) => {}
                TerminatorKind::SwitchDiscriminant { enum_place, .. } => {
                    replace_place(enum_place);
                }
                TerminatorKind::SwitchConstant { place, .. } => {
                    replace_place(place);
                }
                TerminatorKind::Invalid => panic!("invalid terminator found"),
                TerminatorKind::Return { value } => {
                    replace_local(value);
                }
            }
        }
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

/// In MIR, the program is in static single assignment form:
/// each variable is assigned once only. A variable called `target` is
/// typically where we store the result of a statement.
#[derive(Debug, Clone)]
pub enum StatementKind {
    /// Moves an rvalue into a local variable.
    Assign {
        target: LocalVariableName,
        source: Rvalue,
    },
    /// Moves an rvalue into a local variable conditionally,
    /// depending on which block we just came from.
    AssignPhi {
        target: LocalVariableName,
        /// A list of source blocks and the variable that we should move
        /// into `target` if this is where we came from.
        /// In the case that we came from a different block, the given variable will
        /// not have been initialised.
        phi_cases: Vec<(BasicBlockId, LocalVariableName)>,
    },
    /// Creates a local instance of a definition such as a function (or in some cases, a constant).
    /// This statement is removed by the "func_objects" pass, where curried functions are removed.
    InstanceSymbol {
        name: QualifiedName,
        type_variables: Vec<Type>,
        special_case_arguments: Vec<KnownValue>,
        target: LocalVariableName,
    },
    /// Applies one argument to a function, and stores the result in a variable.
    /// This statement is removed by the "func_objects" pass, where curried functions are removed.
    Apply {
        argument: Box<Rvalue>,
        function: Box<Rvalue>,
        target: LocalVariableName,
    },
    /// Invokes a function with the given arguments.
    /// This is inserted by the "func_objects" pass. MIR generation should instead try to generate InstanceSymbol
    /// and Apply statements, and this pass will convert them (where necessary) into this statement.
    InvokeFunction {
        name: QualifiedName,
        type_variables: Vec<Type>,
        special_case_arguments: Vec<KnownValue>,
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
        special_case_arguments: Vec<KnownValue>,
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
    },
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
        name: QualifiedName,
        type_variables: Vec<Type>,
        /// If this type was an enum, which variant should we create?
        variant: Option<String>,
        fields: BTreeMap<String, Rvalue>,
        target: LocalVariableName,
    },
    /// Creates an impl of an aspect from a set of definitions.
    /// The definitions are instanced symbols.
    /// They are considered to be "moved into" the impl for ownership purposes.
    ConstructImpl {
        aspect: QualifiedName,
        type_variables: Vec<Type>,
        definitions: BTreeMap<String, LocalVariableName>,
        target: LocalVariableName,
    },
}

impl Display for StatementKind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StatementKind::Assign { target, source } => write!(f, "{} = {}", target, source),
            StatementKind::AssignPhi { target, phi_cases } => {
                write!(f, "{} = Φ {{", target)?;
                for (id, name) in phi_cases {
                    write!(f, " {} -> {},", id, name)?;
                }
                write!(f, " }}")
            }
            StatementKind::Apply {
                argument,
                function,
                target,
                ..
            } => write!(f, "{} = apply {} to {}", target, argument, function),
            StatementKind::Drop { variable } => write!(f, "drop {}", variable),
            StatementKind::Free { variable } => write!(f, "free {}", variable),
            StatementKind::InstanceSymbol {
                name,
                type_variables,
                special_case_arguments,
                target,
            } => {
                write!(f, "{} = instance {}", target, name)?;
                if !type_variables.is_empty() {
                    write!(f, " with")?;
                    for ty_var in type_variables {
                        write!(f, " {}", ty_var)?;
                    }
                }
                if !special_case_arguments.is_empty() {
                    write!(f, " special case")?;
                    for val in special_case_arguments {
                        write!(f, " {}", val)?;
                    }
                }
                Ok(())
            }
            StatementKind::InvokeFunction {
                name,
                type_variables,
                special_case_arguments,
                target,
                arguments,
            } => {
                write!(f, "{} = invoke {} ( ", target, name)?;
                for arg in special_case_arguments {
                    write!(f, "sc {}, ", arg.display_in_mono())?;
                }
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
                special_case_arguments,
                target,
                curry_steps,
                curried_arguments,
            } => {
                write!(f, "{} = fobj {} ( ", target, name)?;
                for arg in special_case_arguments {
                    write!(f, "sc {}, ", arg.display_in_mono())?;
                }
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
                name,
                type_variables,
                variant,
                fields,
                target,
            } => {
                write!(
                    f,
                    "{} = construct {}",
                    target,
                    Type::Named {
                        name: name.clone(),
                        parameters: type_variables.clone(),
                    }
                )?;
                if let Some(variant) = variant {
                    write!(f, "::{}", variant)?;
                }
                write!(f, " with {{ ")?;
                for (field_name, rvalue) in fields {
                    write!(f, "{} = {}, ", field_name, rvalue)?;
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
    /// If the local is a borrowed type, the result of this projection is a borrowed type with the same borrow condition.
    DataField { field: String },
    /// If the local is a borrowed type, the result of this projection is a borrowed type with the same borrow condition.
    EnumField { variant: String, field: String },
    /// Regardless if the local is a borrowed type or owned type, the result of this projection is an `Int`.
    EnumDiscriminant,
    /// Regardless if the local is a borrowed type or owned type, the result of this projection is an `Int`/`Bool`/other primitive type.
    /// This will repeatedly dereference until the type is primitive.
    Constant,
    /// If the local is a borrowed type, the result of this projection is a borrowed type with the same borrow condition.
    ImplField { field: String },
}

impl Display for PlaceSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceSegment::DataField { field } => write!(f, ".{}", field),
            PlaceSegment::EnumField { variant, field } => write!(f, ".<{}>.{}", variant, field),
            PlaceSegment::EnumDiscriminant => write!(f, ".discriminant"),
            PlaceSegment::Constant => write!(f, ".constant"),
            PlaceSegment::ImplField { field } => write!(f, ".<impl>.{}", field),
        }
    }
}

/// Represents the use of a value that we can feed into an expression or function.
/// We can only read from (not write to) an rvalue.
#[derive(Debug, Clone)]
pub enum Rvalue {
    /// We will move data out of this place, possibly dropping and freeing it.
    Move(Place),
    /// Creates a borrow of a local variable.
    /// Borrowing more complicated things is only an emergent behaviour created by functions.
    /// The borrow's lifetime will be managed later in the borrow checker.
    Borrow(LocalVariableName),
    /// This local variable is a borrow, and we will copy the data behind this place without dropping it.
    /// To create a borrowed value in a local scope, use [Rvalue::Borrow].
    Copy(LocalVariableName),
    /// Generates a new constant value.
    Constant(ConstantValue),
}

impl Display for Rvalue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rvalue::Move(place) => write!(f, "move {}", place),
            Rvalue::Borrow(place) => write!(f, "borrow {}", place),
            Rvalue::Copy(place) => write!(f, "copy {}", place),
            Rvalue::Constant(constant) => write!(f, "const {}", constant),
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
        cases: BTreeMap<String, BasicBlockId>,
    },
    /// Works out which value a given local variable has.
    SwitchConstant {
        /// Where is this value stored?
        place: Place,
        /// Maps the names of constant values to the basic block ID to jump to.
        /// If the constant is a boolean, this must be exhaustive. Otherwise,
        /// there should be a default case to cover missed possibilities.
        cases: BTreeMap<ConstantValue, BasicBlockId>,
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

impl TerminatorKind {
    /// List the targets we could potentially jump to.
    pub fn targets(&self) -> Vec<BasicBlockId> {
        match self {
            TerminatorKind::Goto(target) => vec![*target],
            TerminatorKind::SwitchDiscriminant { cases, .. } => {
                let mut vec = cases.values().copied().collect::<Vec<_>>();
                vec.sort_unstable();
                vec.dedup();
                vec
            }
            TerminatorKind::SwitchConstant { cases, default, .. } => {
                let mut vec = cases
                    .values()
                    .copied()
                    .chain(std::iter::once(*default))
                    .collect::<Vec<_>>();
                vec.sort_unstable();
                vec.dedup();
                vec
            }
            TerminatorKind::Invalid => panic!("can't get targets of invalid terminator"),
            TerminatorKind::Return { .. } => Vec::new(),
        }
    }
}
