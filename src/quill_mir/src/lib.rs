//! This module contains the m range: (), kind: ()id-level intermediate representation of code.
//! Much of this code is heavily inspired by the Rust compiler.

use std::{collections::HashMap, fmt::Display};

use quill_common::{
    diagnostic::DiagnosticResult,
    location::{Range, Ranged},
    name::QualifiedName,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_parser::NameP;
use quill_type::{PrimitiveType, Type};
use quill_type_deduce::type_check::{
    Definition, Expression, ExpressionContentsGeneric, ImmediateValue, Pattern, SourceFileHIR,
};

/// A parsed, type checked, and borrow checked source file.
#[derive(Debug)]
pub struct SourceFileMIR {
    pub definitions: HashMap<String, DefinitionM>,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct ArgumentIndex(pub u64);
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
pub struct LocalVariableId(pub u64);
impl Display for LocalVariableId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "_{}", self.0)
    }
}
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
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
#[derive(Debug)]
pub struct DefinitionM {
    range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<String>,
    /// How many parameters must be supplied to this function? Their types are kept in the local variable names map.
    pub arity: u64,
    /// Contains argument types.
    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
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
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
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
#[derive(Debug)]
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

#[derive(Debug)]
pub struct ControlFlowGraph {
    next_block_id: BasicBlockId,
    /// Every basic block has a unique index, which is its index inside this basic blocks map.
    /// When jumping between basic blocks, we must provide the index of the target block.
    pub basic_blocks: HashMap<BasicBlockId, BasicBlock>,
}

impl ControlFlowGraph {
    /// Inserts a new basic block into the control flow graph, and returns its new unique ID.
    pub fn new_basic_block(&mut self, basic_block: BasicBlock) -> BasicBlockId {
        let id = self.next_block_id;
        self.next_block_id.0 += 1;
        self.basic_blocks.insert(id, basic_block);
        id
    }
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

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} >> {}", self.range, self.kind)
    }
}

#[derive(Debug)]
pub enum StatementKind {
    /// Moves an rvalue into a place.
    Assign { target: Place, source: Rvalue },
    /// Creates a local instance of a definition such as a function (or in some cases, a constant).
    InstanceSymbol {
        name: QualifiedName,
        type_variables: Vec<Type>,
        target: Place,
    },
    /// Applies one argument to a function, and stores the result in a variable.
    Apply {
        argument: Rvalue,
        function: Rvalue,
        target: Place,
    },
    /// Hints to LLVM that this variable's lifetime has now begun, and that we may use this variable later.
    StorageLive(LocalVariableId),
    /// Hints to LLVM that we will no longer use this variable.
    StorageDead(LocalVariableId),
    /// Creates a function object representing a lambda abstraction, capturing variables it uses.
    /// In LIR, this is converted into an external function.
    CreateLambda {
        ty: Type,
        params: Vec<NameP>,
        expr: Box<Expression>,
        target: Place,
    },
    /// Creates an object of a given type, and puts it in target.
    ConstructData {
        ty: Type,
        /// If this type was an enum, which variant should we create?
        variant: Option<String>,
        fields: HashMap<String, Rvalue>,
        target: Place,
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
            } => write!(f, "{} = apply {} to {}", target, argument, function),
            StatementKind::StorageLive(local) => write!(f, "live {}", local),
            StatementKind::StorageDead(local) => write!(f, "dead {}", local),
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
    local: LocalVariableName,
    /// A list of lenses that allow us to index inside this local variable into deeper and deeper nested places.
    projection: Vec<PlaceSegment>,
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
    Field(String),
}

impl Display for PlaceSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PlaceSegment::Field(field) => write!(f, ".{}", field),
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

#[derive(Debug)]
pub struct Terminator {
    pub range: Range,
    pub kind: TerminatorKind,
}

impl Display for Terminator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} >> {}", self.range, self.kind)
    }
}

#[derive(Debug)]
pub enum TerminatorKind {
    /// Jump to another basic block unconditionally.
    Goto(BasicBlockId),
    /// Works out which variant of a enum type a given local variable is.
    SwitchDiscriminator {
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
            TerminatorKind::SwitchDiscriminator { enum_place, cases } => {
                writeln!(f, "switch {} {{", enum_place)?;
                for (case, id) in cases {
                    writeln!(f, "        {} -> {}", case, id)?;
                }
                write!(f, "}}")
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

    pub local_variable_names: HashMap<LocalVariableName, LocalVariableInfo>,
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
        local_variable_names: HashMap::new(),
        local_name_map: HashMap::new(),
        control_flow_graph: ControlFlowGraph {
            next_block_id: BasicBlockId(0),
            basic_blocks: HashMap::new(),
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

    DiagnosticResult::ok(DefinitionM {
        range,
        type_variables,
        arity,
        local_variable_names: ctx.local_variable_names,
        return_type,
        control_flow_graph: ctx.control_flow_graph,
        entry_point,
    })
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
            let (function_block, function_variable) = generate_expr(
                ctx,
                case.replacement,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(return_block),
                },
            );

            // Now, replace the terminator with a custom terminator that returns `function_variable` from the function.
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&return_block)
                .unwrap()
                .terminator = Terminator {
                range,
                kind: TerminatorKind::Return {
                    value: function_variable,
                },
            };

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&unwrap_patterns_block)
                .unwrap()
                .terminator = Terminator {
                range,
                kind: TerminatorKind::Goto(function_block),
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
            // In particular, if two patterns reference *different* variants, then we need to switch the discriminant.
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
                    if let Some(variant) = &type_ctor.variant {
                        // This case applies to exactly one discriminant.
                        cases.get_mut(variant).unwrap().push(i);
                    } else {
                        // This case applies to all discriminants.
                        for (_, case) in cases.iter_mut() {
                            case.push(i);
                        }
                    }
                } else {
                    // This case applies to all discriminants.
                    for (_, case) in cases.iter_mut() {
                        case.push(i);
                    }
                }
            }

            Some(PatternMismatch {
                place: var,
                reason: PatternMismatchReason::EnumDiscriminant { cases },
            })
        } else {
            // This is not an enum, so we now want to consider the first difference *inside* each pattern.
            // We check each field in the data type, and consider how (and if) the patterns differ when reasoning about this field.
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
                    var.clone().then(PlaceSegment::Field(field_name)),
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

/// Creates a basic block (or tree of basic blocks) that
/// performs the given pattern matching operation for an entire function body.
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
        match diff.reason {
            PatternMismatchReason::EnumDiscriminant { cases } => {
                // Create a match operation for each enum discriminant case.
                let cases_matched = cases
                    .into_iter()
                    .map(|(name, cases)| {
                        let new_cases = cases
                            .into_iter()
                            .map(|id| (patterns[id].clone(), blocks[id]))
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
                            enum_place: diff.place,
                            cases: cases_matched,
                        },
                    },
                })
            }
        }
    } else {
        // There was no difference between the patterns.
        // Therefore, there must be exactly one case left unmatched, otherwise we have a case that
        // will *never* be matched, which is an error we emitted earlier in compilation.
        assert!(blocks.len() == 1);
        blocks[0]
    }
}

/// Creates a basic block (or tree of basic blocks) that
/// performs the given pattern matching operation.
/// The value is matched against each case, and basic blocks are created that branch to
/// these 'case' blocks when the pattern is matched. The return value is a basic block
/// which will perform this match operation, then jump to the case blocks.
fn perform_match(
    project_index: &ProjectIndex,
    ctx: &mut DefinitionTranslationContext,
    range: Range,
    value: LocalVariableName,
    ty: Type,
    cases: Vec<(Pattern, BasicBlockId)>,
) -> BasicBlockId {
    // Recursively find the first difference between patterns, until each case has its own branch.
    let (patterns, blocks): (Vec<_>, Vec<_>) = cases.into_iter().unzip();
    if let Some(diff) = first_difference(project_index, Place::new(value), ty.clone(), &patterns) {
        // There was a difference that lets us distinguish some of the patterns into different branches.
        match diff.reason {
            PatternMismatchReason::EnumDiscriminant { cases } => {
                // Create a match operation for each enum discriminant case.
                let cases_matched = cases
                    .into_iter()
                    .map(|(name, cases)| {
                        let new_cases = cases
                            .into_iter()
                            .map(|id| (patterns[id].clone(), blocks[id]))
                            .collect();
                        (
                            name,
                            perform_match(project_index, ctx, range, value, ty.clone(), new_cases),
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
                            enum_place: diff.place,
                            cases: cases_matched,
                        },
                    },
                })
            }
        }
    } else {
        // There was no difference between the patterns.
        // Therefore, there must be exactly one case left unmatched, otherwise we have a case that
        // will *never* be matched, which is an error we emitted earlier in compilation.
        assert!(blocks.len() == 1);
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

/// Generates a chain of expressions, with the given terminator.
/// Returns the basic block that can be invoked in order to invoke the chain, along ith the variables
/// produced by each expression.
fn generate_chain_with_terminator(
    ctx: &mut DefinitionTranslationContext,
    exprs: Vec<Expression>,
    mut terminator: Terminator,
) -> (BasicBlockId, Vec<LocalVariableName>) {
    let range = terminator.range;

    let mut first_block = None;
    let mut locals = Vec::new();

    for expr in exprs.into_iter().rev() {
        let (block, local) = generate_expr(ctx, expr, terminator);
        locals.insert(0, local);
        terminator = Terminator {
            range,
            kind: TerminatorKind::Goto(block),
        };
        first_block = Some(block);
    }

    let first_block = first_block.unwrap_or_else(|| {
        ctx.control_flow_graph.new_basic_block(BasicBlock {
            statements: Vec::new(),
            terminator,
        })
    });

    (first_block, locals)
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
            let storage_live = Statement {
                range: name.range,
                kind: StatementKind::StorageLive(var),
            };
            let assign = Statement {
                range: name.range,
                kind: StatementKind::Assign {
                    target: Place::new(LocalVariableName::Local(var)),
                    source: Rvalue::Use(Operand::Move(value)),
                },
            };

            Some(ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![storage_live, assign],
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
                            .then(PlaceSegment::Field(field_name.name.clone())),
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

/// Generates a basic block that computes the value of this expression, and stores the result in the given local.
/// The block generated will have the given terminator.
fn generate_expr(
    ctx: &mut DefinitionTranslationContext,
    expr: Expression,
    terminator: Terminator,
) -> (BasicBlockId, LocalVariableName) {
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
            (block, variable)
        }
        ExpressionContentsGeneric::Local(local) => {
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });
            let variable = ctx.get_name_of_local(&local.name);
            (block, variable)
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
                        target: Place::new(LocalVariableName::Local(variable)),
                    },
                }],
                terminator,
            });
            (block, LocalVariableName::Local(variable))
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

            let (right_block, right_var) = generate_expr(
                ctx,
                *right,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );
            let (left_block, left_var) = generate_expr(
                ctx,
                *left,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(right_block),
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
                        argument: Rvalue::Use(Operand::Move(Place::new(right_var))),
                        function: Rvalue::Use(Operand::Move(Place::new(left_var))),
                        target: Place::new(LocalVariableName::Local(variable)),
                    },
                });

            (left_block, LocalVariableName::Local(variable))
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
                        expr: substituted_expr,
                        target: Place::new(LocalVariableName::Local(variable)),
                    },
                }],
                terminator,
            });
            (block, LocalVariableName::Local(variable))
        }
        ExpressionContentsGeneric::Let {
            name,
            expr: right_expr,
            ..
        } => {
            // Let expressions return the unit value.

            // Let expressions are handled in two phases. First, (before calling this function)
            // we initialise the context with a blank variable of the right name and type, so that
            // other expressions can access it. Then, we assign a value to the variable in this function now.
            let variable = ctx.get_name_of_local(&name.name);
            let block = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: Vec::new(),
                terminator,
            });

            // Create the RHS of the let expression, and assign it to the LHS.
            let (rvalue_block, rvalue_name) = generate_expr(
                ctx,
                *right_expr,
                Terminator {
                    range,
                    kind: TerminatorKind::Goto(block),
                },
            );

            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&block)
                .unwrap()
                .statements
                .push(Statement {
                    range,
                    kind: StatementKind::Assign {
                        target: Place::new(variable),
                        source: Rvalue::Use(Operand::Move(Place::new(rvalue_name))),
                    },
                });

            (rvalue_block, variable)
        }
        ExpressionContentsGeneric::Block {
            mut statements,
            final_semicolon,
            ..
        } => {
            let final_expression = if final_semicolon.is_none() {
                statements.pop()
            } else {
                None
            };

            if let Some(final_expression) = final_expression {
                let (final_expr_block, variable) = generate_expr(ctx, final_expression, terminator);

                let (previous_block_chain, _) = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(final_expr_block),
                    },
                );

                (previous_block_chain, variable)
            } else {
                // We need to make a new unit variable since there was no final expression.
                // This is the variable that is returned by the block.
                let variable = ctx.new_local_variable(LocalVariableInfo {
                    range,
                    ty: Type::Primitive(PrimitiveType::Unit),
                    name: None,
                });

                // Initialise the variable with an empty value.
                let storage_live = Statement {
                    range,
                    kind: StatementKind::StorageLive(variable),
                };
                let assign = Statement {
                    range,
                    kind: StatementKind::Assign {
                        target: Place::new(LocalVariableName::Local(variable)),
                        source: Rvalue::Use(Operand::Constant(ImmediateValue::Unit)),
                    },
                };

                let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                    statements: vec![storage_live, assign],
                    terminator,
                });

                let (previous_block_chain, _) = generate_chain_with_terminator(
                    ctx,
                    statements,
                    Terminator {
                        range,
                        kind: TerminatorKind::Goto(initialise_variable),
                    },
                );

                (previous_block_chain, LocalVariableName::Local(variable))
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

            // Initialise the variable with its new value.
            let storage_live = Statement {
                range,
                kind: StatementKind::StorageLive(variable),
            };

            let construct_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![storage_live],
                terminator,
            });

            // Chain the construction of the fields.
            let (chained_fields, field_names) = generate_chain_with_terminator(
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
                    fields: field_names
                        .into_iter()
                        .zip(names)
                        .map(|(name, field_name)| {
                            (
                                field_name.name,
                                Rvalue::Use(Operand::Move(Place::new(name))),
                            )
                        })
                        .collect(),
                    target: Place::new(LocalVariableName::Local(variable)),
                },
            };
            ctx.control_flow_graph
                .basic_blocks
                .get_mut(&construct_variable)
                .unwrap()
                .statements
                .push(construct);

            // Finally, chain the construction of the new variable with its fields.

            (chained_fields, LocalVariableName::Local(variable))
        }
        ExpressionContentsGeneric::ImmediateValue { value, range } => {
            let variable = ctx.new_local_variable(LocalVariableInfo {
                range,
                ty,
                name: None,
            });

            // Initialise the variable with an empty value.
            let storage_live = Statement {
                range,
                kind: StatementKind::StorageLive(variable),
            };
            let assign = Statement {
                range,
                kind: StatementKind::Assign {
                    target: Place::new(LocalVariableName::Local(variable)),
                    source: Rvalue::Use(Operand::Constant(value)),
                },
            };

            let initialise_variable = ctx.control_flow_graph.new_basic_block(BasicBlock {
                statements: vec![storage_live, assign],
                terminator,
            });

            (initialise_variable, LocalVariableName::Local(variable))
        }
    }
}
