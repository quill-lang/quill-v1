//! Performs type deduction and type checking of expressions and patterns.

use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Display,
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Location, Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::{ProjectIndex, TypeDeclarationTypeI};
use quill_parser::{DefinitionCaseP, ExprPatP, FileP, NameP};
use quill_type::Type;

use crate::{
    index_resolve::{
        replace_type_variables, resolve_definition, resolve_type_constructor,
        TypeConstructorInvocation,
    },
    type_deduce::deduce_expr_type,
    type_resolve::TypeVariableId,
};

/// A parsed and fully type checked file_parsed.
/// No effort has been made to ensure semantic consistency or correctness,
/// just syntactic and type correctness.
#[derive(Debug)]
pub struct Module {
    pub definitions: HashMap<String, Definition>,
}

impl Display for Module {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Definitions:")?;
        for (def_name, def) in &self.definitions {
            writeln!(f, "  {} : {}", def_name, def.symbol_type)?;
        }
        Ok(())
    }
}

/// A definition for a symbol, i.e. a function or constant.
#[derive(Debug)]
pub struct Definition {
    range: Range,
    /// The type variables at the start of this definition.
    pub type_variables: Vec<String>,
    pub symbol_type: Type,
    pub cases: Vec<DefinitionCase>,
}

impl Ranged for Definition {
    fn range(&self) -> Range {
        self.range
    }
}

#[derive(Debug)]
pub struct DefinitionCase {
    range: Range,
    pub arg_patterns: Vec<Pattern>,
    pub replacement: Expression,
}

/// A pattern made up of type constructors and potential unknowns.
#[derive(Debug, Clone)]
pub enum Pattern {
    /// A name representing the entire pattern, e.g. `a`.
    Named(NameP),
    /// A type constructor, e.g. `False` or `Maybe { value = a }`.
    TypeConstructor {
        type_ctor: TypeConstructorInvocation,
        /// The list of fields. If a pattern is provided, the pattern is matched against the named field.
        /// If no pattern is provided, an automatic pattern is created, that simply assigns the field to a new variable with the same name.
        fields: Vec<(NameP, Pattern)>,
    },
    /// A function pattern. This cannot be used directly in code,
    /// this is created only for working with functions that have multiple patterns.
    Function {
        param_types: Vec<Type>,
        args: Vec<Pattern>,
    },
    /// An underscore representing an ignored pattern.
    Unknown(Range),
}

impl Ranged for Pattern {
    fn range(&self) -> Range {
        match self {
            Pattern::Named(identifier) => identifier.range,
            Pattern::TypeConstructor {
                type_ctor,
                fields: args,
            } => args
                .iter()
                .fold(type_ctor.range, |acc, (_name, pat)| acc.union(pat.range())),
            Pattern::Unknown(range) => *range,
            Pattern::Function { args, .. } => args
                .iter()
                .fold(args[0].range(), |acc, i| acc.union(i.range())),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Named(identifier) => write!(f, "{}", identifier.name),
            Pattern::TypeConstructor {
                type_ctor,
                fields: args,
            } => {
                if args.is_empty() {
                    return write!(f, "{}", type_ctor.type_ctor);
                }

                write!(f, "{} {{ ", type_ctor.type_ctor)?;
                for (i, (name, pat)) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, " {}", name.name)?;
                    write!(f, " = {}", pat)?;
                }
                write!(f, " }}")
            }
            Pattern::Function { args, .. } => {
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", arg)?;
                }
                Ok(())
            }
            Pattern::Unknown(_) => write!(f, "_"),
        }
    }
}

/// Used to determine whether sets of patterns are exhaustive or not.
#[derive(Debug)]
struct PatternExhaustionCheck {
    /// Unmatched patterns should be treated as if in file name "" at location (0, 0).
    unmatched_patterns: Vec<Pattern>,
}

impl PatternExhaustionCheck {
    /// Adds the given pattern to this pattern check, excluding this pattern from all as yet `unmatched_patterns`.
    /// If anything was modified, return true.
    pub fn add(&mut self, project_index: &ProjectIndex, to_exclude: &Pattern) -> bool {
        let mut anything_modified = false;
        for pat in std::mem::take(&mut self.unmatched_patterns) {
            let (modified, mut new_internal_patterns) =
                PatternExhaustionCheck::exclude_pattern(project_index, pat, to_exclude);
            if modified {
                anything_modified = true;
            }
            self.unmatched_patterns.append(&mut new_internal_patterns);
        }
        anything_modified
    }

    /// This function returns all patterns that match `pat` but do not match `to_exclude`; and returns true if some refinement to the pattern happened.
    /// In the simplest case, when the two patterns are orthogonal, this returns `(false, vec![pat])`.
    /// If `to_exclude` matches `pat` completely, then this returns `(true, Vec::new())`.
    /// If `to_exclude` matches some subset of `pat`, then `true` and the complement of this subset is returned.
    fn exclude_pattern(
        project_index: &ProjectIndex,
        pat: Pattern,
        to_exclude: &Pattern,
    ) -> (bool, Vec<Pattern>) {
        match pat {
            Pattern::Named(_) => (
                true,
                PatternExhaustionCheck::complement(project_index, to_exclude),
            ),
            pat @ Pattern::TypeConstructor { .. } => {
                // If we have a type constructor e.g. `Type a b`, and we want to exclude `Type c d`,
                // the resultant patterns are intersection(`Type a b`, complement(`Type c d`)).
                let mut anything_changed = false;
                let mut results = Vec::new();
                for pat_to_exclude in PatternExhaustionCheck::complement(project_index, to_exclude)
                {
                    let (changed, result) = PatternExhaustionCheck::intersection(
                        project_index,
                        pat.clone(),
                        pat_to_exclude,
                    );
                    if changed {
                        anything_changed = true;
                    }
                    if let Some(result) = result {
                        results.push(result);
                    }
                }
                (anything_changed, results)
            }
            pat @ Pattern::Function { .. } => {
                // If we have a function e.g. `add a b`, and we want to exclude `add c d`,
                // the resultant patterns are intersection(`add a b`, complement(`add c d`)).
                let mut anything_changed = false;
                let mut results = Vec::new();
                for pat_to_exclude in PatternExhaustionCheck::complement(project_index, to_exclude)
                {
                    let (changed, result) = PatternExhaustionCheck::intersection(
                        project_index,
                        pat.clone(),
                        pat_to_exclude,
                    );
                    if changed {
                        anything_changed = true;
                    }
                    if let Some(result) = result {
                        results.push(result);
                    }
                }
                // If the results list is empty, then there was a change - namely, there was no complement,
                // and therefore there is no intersection.
                (anything_changed || results.is_empty(), results)
            }
            Pattern::Unknown(_) => (
                true,
                PatternExhaustionCheck::complement(project_index, to_exclude),
            ),
        }
    }

    /// Returns all patterns of the same type that did not match the given pattern.
    fn complement(project_index: &ProjectIndex, pat: &Pattern) -> Vec<Pattern> {
        match pat {
            Pattern::Named(_) => {
                // A named pattern, e.g. `a`, matches anything.
                Vec::new()
            }
            Pattern::TypeConstructor { type_ctor, fields } => {
                // A type constructor, e.g. `Just { value = 3 }` does not match:
                // - `Just { value = a }` where `a` is in the complement of `3`
                // - `a` where `a` is any other type constructor for the same type.
                let data_type_decl = &project_index[&type_ctor.data_type.source_file].types
                    [&type_ctor.data_type.name];
                let TypeDeclarationTypeI::Data(datai) = &data_type_decl.decl_type;
                // Loop through all of the type constructors.
                let mut complement = Vec::new();
                for known_type_ctor in &datai.type_ctors {
                    if known_type_ctor.name == type_ctor.type_ctor {
                        // This is the type constructor we want to find the complement of.
                        // The complement of a type constructor e.g. `Foo { a, b, c }` is the intersection of all possible combinations of
                        // complements of a, b and c except for `Foo { a, b, c }` itself. In this example, it would be
                        // - Foo { comp(a), _, _ }
                        // - Foo { a, comp(b), _ }
                        // - Foo { a, b, comp(c) }
                        complement.extend(
                            PatternExhaustionCheck::complement_fields(project_index, fields)
                                .into_iter()
                                .map(|arg_list| Pattern::TypeConstructor {
                                    type_ctor: TypeConstructorInvocation {
                                        data_type: type_ctor.data_type.clone(),
                                        type_ctor: known_type_ctor.name.clone(),
                                        range: Location { line: 0, col: 0 }.into(),
                                        num_parameters: type_ctor.num_parameters,
                                    },
                                    fields: arg_list,
                                }),
                        );
                    } else {
                        // Instance a generic pattern for this type constructor.
                        complement.push(Pattern::TypeConstructor {
                            type_ctor: TypeConstructorInvocation {
                                data_type: type_ctor.data_type.clone(),
                                type_ctor: known_type_ctor.name.clone(),
                                range: Location { line: 0, col: 0 }.into(),
                                num_parameters: type_ctor.num_parameters,
                            },
                            fields: known_type_ctor
                                .fields
                                .iter()
                                .map(|(name, _ty)| {
                                    (
                                        name.clone(),
                                        Pattern::Unknown(Location { line: 0, col: 0 }.into()),
                                    )
                                })
                                .collect(),
                        });
                    }
                }
                complement
            }
            Pattern::Function { param_types, args } => {
                // The complement of a function invocation e.g. `foo a b c` is the intersection of all possible combinations of
                // complements of a, b and c except for `foo a b c` itself. In this example, it would be
                // - foo comp(a) _ _
                // - foo a comp(b) _
                // - foo a b comp(c)
                PatternExhaustionCheck::complement_args(project_index, args)
                    .into_iter()
                    .map(|arg_list| Pattern::Function {
                        param_types: param_types.clone(),
                        args: arg_list,
                    })
                    .collect()
            }
            Pattern::Unknown(_) => {
                // An unknown pattern, e.g. `_`, matches anything.
                Vec::new()
            }
        }
    }

    /// See `Pattern::Function` case in `complement`.
    /// This takes every possible case of an argument and its complement, excluding the case without any complements.
    /// Returns a list of all possible argument lists.
    /// The complement of `a = True, b = True, c = True` returned by this function is `False _ _`, `True False _`, `True True False`.
    fn complement_fields(
        project_index: &ProjectIndex,
        args: &[(NameP, Pattern)],
    ) -> Vec<Vec<(NameP, Pattern)>> {
        let mut complements = Vec::new();
        for i in 0..args.len() {
            // This argument will become its complement.
            // Prior arguments are cloned, and future arguments are ignored.
            let (name, original_pattern) = &args[i];
            for complement in PatternExhaustionCheck::complement(project_index, original_pattern) {
                let mut new_args = Vec::new();
                for arg in &args[0..i] {
                    new_args.push(arg.clone());
                }
                new_args.push((name.clone(), complement));
                for (arg_name, _) in args.iter().skip(i) {
                    new_args.push((
                        arg_name.clone(),
                        Pattern::Unknown(Location { line: 0, col: 0 }.into()),
                    ));
                }
                complements.push(new_args);
            }
        }
        complements
    }

    /// See `Pattern::Function` case in `complement`.
    /// This takes every possible case of an argument and its complement, excluding the case without any complements.
    /// Returns a list of all possible argument lists.
    /// The complement of `True True True` returned by this function is `False _ _`, `True False _`, `True True False`.
    fn complement_args(project_index: &ProjectIndex, args: &[Pattern]) -> Vec<Vec<Pattern>> {
        let mut complements = Vec::new();
        for i in 0..args.len() {
            // This argument will become its complement.
            // Prior arguments are cloned, and future arguments are ignored.
            for complement in PatternExhaustionCheck::complement(project_index, &args[i]) {
                let mut new_args = Vec::new();
                for arg in &args[0..i] {
                    new_args.push(arg.clone());
                }
                new_args.push(complement);
                for _ in (i + 1)..args.len() {
                    new_args.push(Pattern::Unknown(Location { line: 0, col: 0 }.into()));
                }
                complements.push(new_args);
            }
        }
        complements
    }

    /// Returns the pattern that matched both patterns, if such a pattern existed.
    /// Returns false if no pattern deduction occured (i.e., if we return pat1).
    fn intersection(
        project_index: &ProjectIndex,
        pat1: Pattern,
        pat2: Pattern,
    ) -> (bool, Option<Pattern>) {
        match pat1 {
            Pattern::Named(_) => {
                // A named pattern matches anything, so return just pat2.
                // If pat2 is `Named` or `Unknown`, no deduction occured.
                (
                    !matches!(pat2, Pattern::Named(_) | Pattern::Unknown(_)),
                    Some(pat2),
                )
            }
            Pattern::TypeConstructor {
                type_ctor: type_ctor1,
                fields: args1,
            } => {
                match pat2 {
                    Pattern::TypeConstructor {
                        type_ctor: type_ctor2,
                        fields: args2,
                    } => {
                        if type_ctor1.type_ctor == type_ctor2.type_ctor {
                            // If the type constructors are the same, the intersection is just the intersection of their args.
                            let mut anything_modified = false;
                            let mut fields = Vec::new();
                            for (name1, pat1) in &args1 {
                                for (name2, pat2) in &args2 {
                                    if name1.name != name2.name {
                                        continue;
                                    }

                                    let (modified, new_arg) = PatternExhaustionCheck::intersection(
                                        project_index,
                                        pat1.clone(),
                                        pat2.clone(),
                                    );
                                    if modified {
                                        anything_modified = true;
                                    }
                                    match new_arg {
                                        Some(new_arg) => fields.push((name1.clone(), new_arg)),
                                        // If None, no intersection was found between the arguments, so there is no intersection between the main patterns.
                                        None => return (true, None),
                                    }
                                }
                            }
                            (
                                anything_modified,
                                Some(Pattern::TypeConstructor {
                                    type_ctor: type_ctor1,
                                    fields,
                                }),
                            )
                        } else {
                            // If the type constructors are different, the intersection is empty.
                            (true, None)
                        }
                    }
                    Pattern::Named(_) | Pattern::Unknown(_) => (
                        false,
                        Some(Pattern::TypeConstructor {
                            type_ctor: type_ctor1,
                            fields: args1,
                        }),
                    ),
                    _ => panic!("was not type constructor {:#?}", pat2),
                }
            }
            Pattern::Function {
                param_types,
                args: args1,
            } => {
                if let Pattern::Function { args: args2, .. } = pat2 {
                    // The intersection is just the intersection of the functions' arguments.
                    let mut anything_modified = false;
                    let mut args = Vec::new();
                    for (arg1, arg2) in args1.into_iter().zip(args2) {
                        let (modified, new_arg) =
                            PatternExhaustionCheck::intersection(project_index, arg1, arg2);
                        if modified {
                            anything_modified = true;
                        }
                        match new_arg {
                            Some(new_arg) => args.push(new_arg),
                            // If None, no intersection was found between the arguments, so there is no intersection between the main patterns.
                            None => return (true, None),
                        }
                    }
                    (
                        anything_modified,
                        Some(Pattern::Function { param_types, args }),
                    )
                } else {
                    panic!("was not function")
                }
            }
            Pattern::Unknown(_) => {
                // An unknown pattern matches anything, so return just pat2.
                // If pat2 is `Named` or `Unknown`, no deduction occured.
                (
                    !matches!(pat2, Pattern::Named(_) | Pattern::Unknown(_)),
                    Some(pat2),
                )
            }
        }
    }
}

pub fn check(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    file_parsed: FileP,
) -> DiagnosticResult<Module> {
    let type_checker = TypeChecker {
        source_file,
        project_index,
        messages: Vec::new(),
    };
    type_checker.compute(file_parsed)
}

struct TypeChecker<'a> {
    source_file: &'a SourceFileIdentifier,
    project_index: &'a ProjectIndex,

    messages: Vec<ErrorMessage>,
}

/// A variable bound by the definition of a function.
#[derive(Debug, Clone)]
pub struct BoundVariable {
    pub range: Range,
    pub var_type: Type,
}

/// A variable bound by some abstraction e.g. a lambda or a let inside it.
#[derive(Debug, Clone)]
pub struct AbstractionVariable {
    pub range: Range,
    pub var_type: TypeVariableId,
}

#[derive(Debug)]
pub struct ExpressionT {
    pub type_variable: TypeVariable,
    pub contents: ExpressionContentsT,
}

impl Ranged for ExpressionT {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Closely tied to the `Type` struct, this is used while type checking to allow
/// unknown types, represented by `TypeVariableId`s.
#[derive(Debug, Clone)]
pub enum TypeVariable {
    /// An explicitly named type possibly with type parameters, e.g. `Bool` or `Either[T, U]`.
    Named {
        name: QualifiedName,
        parameters: Vec<TypeVariable>,
    },
    Function(Box<TypeVariable>, Box<TypeVariable>),
    /// A known type variable, e.g. `T` or `F[A]`.
    Variable {
        variable: String,
        parameters: Vec<TypeVariable>,
    },
    /// A completely unknown type - we don't even have a type variable letter to describe it such as `T`.
    /// These are assigned random IDs, and when printed are converted into Greek letters using the
    /// `TypeVariablePrinter`.
    Unknown {
        id: TypeVariableId,
    },
}

/// A utility for printing type variables to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct TypeVariablePrinter {
    /// Maps type variable IDs to the names we use to render them.
    type_variable_names: HashMap<TypeVariableId, String>,
    /// When we see a new type variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
    /// A substitution mapping type variables to the substituted type variable.
    /// This map is tried before making a new name for a type variable.
    substitution: HashMap<TypeVariableId, TypeVariable>,
}

impl TypeVariablePrinter {
    pub fn new(substitution: HashMap<TypeVariableId, TypeVariable>) -> Self {
        Self {
            type_variable_names: HashMap::new(),
            type_variable_name: 0,
            substitution,
        }
    }

    pub fn print(&mut self, ty: TypeVariable) -> String {
        match ty {
            TypeVariable::Named { name, parameters } => {
                let mut result = name.name;
                if !parameters.is_empty() {
                    result += "[";
                    for (i, param) in parameters.into_iter().enumerate() {
                        if i != 0 {
                            result += ", ";
                        }
                        result += &self.print(param);
                    }
                    result += "]";
                }
                result
            }
            TypeVariable::Function(l, r) => {
                // TODO sort out precedence
                format!("{} -> ({})", self.print(*l), self.print(*r))
            }
            TypeVariable::Unknown { id } => self.get_name(&id),
            TypeVariable::Variable {
                variable,
                parameters,
            } => {
                let mut result = variable;
                if !parameters.is_empty() {
                    result += "[";
                    for (i, param) in parameters.into_iter().enumerate() {
                        if i != 0 {
                            result += ", ";
                        }
                        result += &self.print(param);
                    }
                    result += "]";
                }
                result
            }
        }
    }

    fn get_name(&mut self, ty: &TypeVariableId) -> String {
        if let Some(result) = self.substitution.get(ty) {
            let cloned = result.clone();
            // If the substitution doesn't do anything, don't stick in an infinite loop.
            // We don't need to worry about cycles - the substitution is defined to be idempotent.
            if let TypeVariable::Unknown { id: other_id } = cloned {
                if other_id == *ty {
                    // The substitution exists, but maps the value to itself.
                } else {
                    return self.print(TypeVariable::Unknown { id: other_id });
                }
            } else {
                return self.print(cloned);
            }
        }
        if let Some(result) = self.type_variable_names.get(&ty) {
            return result.clone();
        }
        let name = self.new_name();
        self.type_variable_names.insert(*ty, name.clone());
        name
    }

    fn new_name(&mut self) -> String {
        let id = self.type_variable_name;
        self.type_variable_name += 1;

        // Assign a new lowercase Greek letter to this type.
        // There are 24 letters to choose from.
        // If we overflow this, just add a suffix to the name.
        let name = std::char::from_u32('α' as u32 + (id % 24)).unwrap();
        let suffix = id / 24;
        if suffix > 0 {
            format!("<{}{}>", name, suffix)
        } else {
            format!("<{}>", name)
        }
    }
}

#[derive(Debug)]
pub struct Expression {
    pub ty: Type,
    pub contents: ExpressionContents,
}

impl Ranged for Expression {
    fn range(&self) -> Range {
        self.contents.range()
    }
}

/// Represents the contents of an expression (which may or may not have been already type checked).
/// The type `T` represents the type variables that we are substituting into this symbol.
/// You should use `ExpressionContents` or `ExpressionContentsT` instead of this enum directly.
#[derive(Debug)]
pub enum ExpressionContentsGeneric<E, T> {
    /// An argument to this function e.g. `x`.
    Argument(NameP),
    /// A local variable declared by a `lambda` expression.
    MonotypeVariable(NameP),
    /// A local variable declared by a `let` expression.
    PolytypeVariable(NameP),
    /// A symbol in global scope e.g. `+` or `fold`.
    Symbol {
        /// The name that the symbol refers to.
        name: QualifiedName,
        /// The range where the symbol's name was written in this file.
        range: Range,
        /// The type variables we're substituting into this symbol.
        /// If using an `ExpressionT`, this should be a vector of `TypeVariable`.
        /// If using an `Expression`, this should be a vector of `Type`.
        type_variables: T,
    },
    /// Apply the left hand side to the right hand side, e.g. `a b`.
    /// More complicated expressions e.g. `a b c d` can be desugared into `((a b) c) d`.
    Apply(Box<E>, Box<E>),
    /// A lambda abstraction, specifically `lambda params -> expr`.
    Lambda {
        lambda_token: Range,
        params: Vec<NameP>,
        expr: Box<E>,
    },
    /// A let statement, specifically `let identifier = expr;`.
    Let {
        let_token: Range,
        name: NameP,
        expr: Box<E>,
    },
    /// A block of statements, inside parentheses, separated by semicolons,
    /// where the final expression in the block is the type of the block as a whole.
    /// If a semicolon is included as the last token in the block, the block implicitly returns the unit type instead;
    /// in this case, the `final_semicolon` variable contains this semicolon and the block's return type is considered to just be unit.
    Block {
        open_bracket: Range,
        close_bracket: Range,
        statements: Vec<E>,
        final_semicolon: Option<Range>,
    },
    /// Explicitly create a value of a data type.
    ConstructData {
        data_type_name: QualifiedName,
        type_ctor: String,
        fields: Vec<(NameP, E)>,
        open_brace: Range,
        close_brace: Range,
    },
}

impl<E, T> Ranged for ExpressionContentsGeneric<E, T>
where
    E: Ranged,
{
    fn range(&self) -> Range {
        match self {
            ExpressionContentsGeneric::Argument(arg) => arg.range,
            ExpressionContentsGeneric::MonotypeVariable(var) => var.range,
            ExpressionContentsGeneric::PolytypeVariable(var) => var.range,
            ExpressionContentsGeneric::Symbol { range, .. } => *range,
            ExpressionContentsGeneric::Apply(l, r) => l.range().union(r.range()),
            ExpressionContentsGeneric::Lambda {
                lambda_token, expr, ..
            } => lambda_token.union(expr.range()),
            ExpressionContentsGeneric::Let {
                let_token, expr, ..
            } => let_token.union(expr.range()),
            ExpressionContentsGeneric::ConstructData {
                open_brace,
                close_brace,
                ..
            } => open_brace.union(*close_brace),
            ExpressionContentsGeneric::Block {
                open_bracket,
                close_bracket,
                ..
            } => open_bracket.union(*close_bracket),
        }
    }
}

pub type ExpressionContents = ExpressionContentsGeneric<Expression, Vec<Type>>;
pub type ExpressionContentsT =
    ExpressionContentsGeneric<ExpressionT, HashMap<String, TypeVariableId>>;

impl<'a> TypeChecker<'a> {
    fn compute(mut self, file_parsed: FileP) -> DiagnosticResult<Module> {
        let mut definitions = HashMap::<String, Definition>::new();

        for definition in file_parsed.definitions {
            let cases = definition.cases;
            let def_name = definition.name;
            let type_parameters = definition.type_parameters;

            // Let's type check the function signature.
            let symbol = &self.project_index[self.source_file].definitions[&def_name.name];
            let symbol_type = &symbol.symbol_type;

            // We need to check pattern exhaustiveness in the definition's cases.
            // Let's resolve each case's patterns and expressions.
            let cases = cases
                .into_iter()
                .map(|case| self.resolve_case(&def_name.name, case))
                .collect::<DiagnosticResult<_>>();

            // Now we can check whether the patterns are valid.
            let cases_validated = cases.bind(|cases| {
                cases
                    .into_iter()
                    .map(|(range, args, replacement)| {
                        self.validate_case(&symbol_type, range, args, replacement, def_name.range)
                    })
                    .collect::<DiagnosticResult<_>>()
            });
            // Check that the patterns we have generated are exhaustive.
            let validated = cases_validated.deny().bind(|cases_validated| {
                self.check_cases_exhaustive(
                    &symbol_type,
                    cases_validated
                        .iter()
                        .map(|(range, pat, _)| (*range, pat))
                        .collect(),
                    &def_name,
                )
                .map(|_| cases_validated)
            });

            let (definition_parsed, mut inner_messages) = validated.destructure();
            self.messages.append(&mut inner_messages);
            if let Some(cases) = definition_parsed {
                definitions.insert(
                    def_name.name,
                    Definition {
                        range: def_name.range,
                        type_variables: type_parameters
                            .iter()
                            .map(|id| id.name.name.clone())
                            .collect(),
                        symbol_type: symbol_type.clone(),
                        cases: cases
                            .into_iter()
                            .map(|(range, arg_patterns, replacement)| DefinitionCase {
                                range,
                                arg_patterns,
                                replacement,
                            })
                            .collect(),
                    },
                );
            }
        }

        /*for data in file_parsed.data {
            let type_params = data
                .type_params
                .iter()
                .map(|id| id.name.name.clone())
                .collect::<Vec<String>>();
            let data_type_name = QualifiedName {
                source_file: self.source_file.clone(),
                name: data.identifier.name.clone(),
                range: data.identifier.range,
            };
            let data_type = Type::Named {
                name: data_type_name.clone(),
                parameters: data
                    .type_params
                    .iter()
                    .map(|id| Type::Variable {
                        variable: id.name.name.clone(),
                        parameters: Vec::new(),
                    })
                    .collect(),
            };

            for type_ctor in data.type_ctors {
                let symbol_type = self.project_index[self.source_file].definitions[&type_ctor.name.name]
                    .symbol_type
                    .clone();
                let (arg_types, _) =
                    get_args_of_type_arity(&symbol_type, type_ctor.fields.len());

                let case = DefinitionCase {
                    range: type_ctor.id.range,
                    arg_patterns: type_ctor
                        .arguments
                        .iter()
                        .enumerate()
                        .map(|(i, ty)| {
                            Pattern::Named(NameP {
                                name: format!("_{}", i),
                                range: ty.range(),
                            })
                        })
                        .collect(),
                    replacement: Expression {
                        ty: data_type.clone(),
                        contents: ExpressionContents::CreateData {
                            data_type_name: data_type_name.clone(),
                            type_ctor: type_ctor.id.name.clone(),
                            args: type_ctor
                                .arguments
                                .iter()
                                .enumerate()
                                .map(|(i, ty)| Expression {
                                    ty: arg_types[i].clone(),
                                    contents: ExpressionContents::Argument(NameP {
                                        name: format!("_{}", i),
                                        range: ty.range(),
                                    }),
                                })
                                .collect(),
                        },
                    },
                };

                let definition = Definition {
                    range: type_ctor.id.range,
                    quantifiers: type_params.clone(),
                    symbol_type,
                    cases: vec![case],
                };
                definitions.insert(type_ctor.id.name, definition);
            }
        }*/

        DiagnosticResult::ok_with_many(Module { definitions }, self.messages)
    }

    fn resolve_case(
        &self,
        function_name: &str,
        case: DefinitionCaseP,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, ExprPatP)> {
        let range = case.pattern.range();
        let pattern = self.resolve_func_pattern(function_name, case.pattern);
        let replacement = case.replacement;
        pattern.map(|pattern| (range, pattern, replacement))
    }

    /// Verify that the given case exactly matches the required type, and also type check the expression given the arguments' types and the expected output type.
    fn validate_case(
        &self,
        symbol_type: &Type,
        range: Range,
        args: Vec<Pattern>,
        replacement: ExprPatP,
        definition_identifier_range: Range,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, Expression)> {
        let (symbol_args, _) = get_args_of_type(symbol_type);
        // The types in `args` must match the first `args.len()` types in symbol_args.
        if args.len() > symbol_args.len() {
            return DiagnosticResult::fail(ErrorMessage::new(
                String::from("too many arguments given to function"),
                Severity::Error,
                Diagnostic::at(self.source_file, &args[symbol_args.len()]),
            ));
        }
        // Let's recalculate symbol_args and result to match the number of arguments we supplied.
        let (symbol_args, result) = get_args_of_type_arity(symbol_type, args.len());

        // Now we can check that the types provided in `args` match the expected `symbol_args`.
        let arg_vars = args
            .iter()
            .zip(symbol_args.into_iter())
            .map(|(pattern, expected_type)| self.match_and_bind(pattern, expected_type))
            .collect::<DiagnosticResult<_>>();
        // Collect the list of maps into a single map, ensuring that we don't have duplicate variable names.
        let arg_vars = arg_vars.bind(|arg_vars| collect_bound_vars(self.source_file, arg_vars));

        // Now, parse the expression, now that we know the input variable types.
        arg_vars
            .bind(|arg_vars| {
                deduce_expr_type(
                    self.source_file,
                    self.project_index,
                    &arg_vars,
                    replacement,
                    result,
                    definition_identifier_range,
                )
            })
            .map(|expr| (range, args, expr))
    }

    /// Match the pattern to the type. If the pattern is a match for the type, a map is returned which
    /// shows what variable names have what types.
    fn match_and_bind(
        &self,
        pattern: &Pattern,
        expected_type: Type,
    ) -> DiagnosticResult<HashMap<String, BoundVariable>> {
        match pattern {
            Pattern::Named(identifier) => {
                let mut map = HashMap::new();
                map.insert(
                    identifier.name.clone(),
                    BoundVariable {
                        var_type: expected_type,
                        range: identifier.range,
                    },
                );
                DiagnosticResult::ok(map)
            }
            Pattern::TypeConstructor {
                type_ctor,
                fields: provided_fields,
            } => match expected_type {
                Type::Named {
                    name: expected_name,
                    parameters: concrete_type_parameters,
                } => {
                    if type_ctor.data_type == expected_name {
                        // Find the data type declaration in the index.
                        let data_type_decl = &self.project_index[&expected_name.source_file].types
                            [&expected_name.name];
                        // Find the original list of named type parameters.
                        // For instance, in a data type `Foo[A]`, the named type parameter list is `[A]`.
                        // We can then create a bijective correspondence between the list of `concrete_type_parameters` given
                        // and the list of `named_type_parameters`, so we can identify which type parameter has which value.
                        // Also, find the list of fields for the type constructor that we're creating.
                        let (named_type_parameters, expected_fields) = {
                            let TypeDeclarationTypeI::Data(datai) = &data_type_decl.decl_type;
                            let mut fields = None;
                            for ctor in &datai.type_ctors {
                                if ctor.name == type_ctor.type_ctor {
                                    fields = Some(
                                        ctor.fields
                                            .iter()
                                            .map(|(name, ty)| (name.name.clone(), ty.clone()))
                                            .collect::<HashMap<String, Type>>(),
                                    );
                                }
                            }
                            if let Some(fields) = fields {
                                (&datai.type_params, fields)
                            } else {
                                return DiagnosticResult::fail(ErrorMessage::new(
                                    "could not find a type constructor with this name".to_string(),
                                    Severity::Error,
                                    Diagnostic::at(self.source_file, &type_ctor.range),
                                ));
                            }
                        };

                        // Process the fields provided to this type constructor.
                        let provided_fields = provided_fields
                            .iter()
                            .map(|(name, pat)| (name.name.clone(), pat.clone()))
                            .collect::<HashMap<String, Pattern>>();

                        // Check that the names of the provided fields and the expected fields match.
                        let mut bound_vars = Vec::new();
                        for (field_name, pattern) in &provided_fields {
                            // Does this field actually belong to the type constructor?
                            if let Some(field_type) = expected_fields.get(field_name) {
                                // For each field in the constructor, we need to match that field against the known type
                                // of this field. So we need to match the type parameters in this type constructor
                                // against the type parameters above.
                                // This means that when matching a `Maybe Bool`, the type constructor `Just { value: T }` becomes `Just { value: Bool }`,
                                // because the `T` is replaced with the concrete type `Bool`.
                                let expected_type = replace_type_variables(
                                    field_type.clone(),
                                    named_type_parameters,
                                    &concrete_type_parameters,
                                );
                                bound_vars.push(self.match_and_bind(pattern, expected_type));
                            }
                        }
                        DiagnosticResult::sequence(bound_vars)
                            .bind(|bound_vars| collect_bound_vars(self.source_file, bound_vars))
                            .bind(|result| {
                                // Check that all of the fields were actually referenced.
                                let mut messages = Vec::new();
                                for field_name in expected_fields.keys() {
                                    if !provided_fields.contains_key(field_name) {
                                        messages.push(ErrorMessage::new(
                                            format!(
                                                "this pattern is missing the field `{}`",
                                                field_name
                                            ),
                                            Severity::Error,
                                            Diagnostic::at(self.source_file, &type_ctor.range),
                                        ))
                                    }
                                }
                                DiagnosticResult::ok_with_many(result, messages)
                            })
                    } else {
                        DiagnosticResult::fail(ErrorMessage::new(
                            format!("expected a type constructor for `{}`", expected_name),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &type_ctor.range),
                        ))
                    }
                }
                Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected a name for a function, not a type constructor"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &type_ctor.range),
                )),
                Type::Variable { variable, .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected a name for a variable of type `{}`, not a type constructor",
                        variable
                    ),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &type_ctor.range),
                )),
            },
            Pattern::Unknown(_) => DiagnosticResult::ok(HashMap::new()),
            Pattern::Function { .. } => unimplemented!(),
        }
    }

    fn check_cases_exhaustive(
        &self,
        symbol_type: &Type,
        cases: Vec<(Range, &Vec<Pattern>)>,
        def_ident: &NameP,
    ) -> DiagnosticResult<()> {
        // Check that all cases have the same amount of arguments.
        let arg_count = cases[0].1.len();
        let mismatched_cases = cases
            .iter()
            .filter(|(_, args)| args.len() != arg_count)
            .collect::<Vec<_>>();
        if !mismatched_cases.is_empty() {
            let error_messages = mismatched_cases
                .into_iter()
                .map(|(case_range, _)| {
                    ErrorMessage::new_with(
                        String::from("patterns had different amounts of arguments"),
                        Severity::Error,
                        Diagnostic::at(self.source_file, case_range),
                        HelpMessage {
                            message: format!("expected {} to match first pattern", arg_count),
                            help_type: HelpType::Note,
                            diagnostic: Diagnostic::at(self.source_file, &cases[0].0),
                        },
                    )
                })
                .collect::<Vec<_>>();
            return DiagnosticResult::fail_many(error_messages);
        }

        // Now, let's begin gradually refining the patterns for each argument until exhaustion is determined.
        let (symbol_args, _) = get_args_of_type_arity(symbol_type, arg_count);
        let mut args_exhaustion = PatternExhaustionCheck {
            unmatched_patterns: vec![Pattern::Function {
                param_types: symbol_args.clone(),
                args: (0..arg_count)
                    .map(|_| Pattern::Unknown(Location { line: 0, col: 0 }.into()))
                    .collect(),
            }],
        };

        let mut messages = Vec::new();
        for (range, patterns) in &cases {
            let pattern = Pattern::Function {
                param_types: symbol_args.clone(),
                args: (*patterns).clone(),
            };
            let anything_modified = args_exhaustion.add(self.project_index, &pattern);
            if !anything_modified {
                messages.push(ErrorMessage::new(
                    String::from("this pattern will never be matched"),
                    Severity::Warning,
                    Diagnostic::at(self.source_file, range),
                ));
            }
        }
        if !args_exhaustion.unmatched_patterns.is_empty() {
            let mut message = String::from(
                "the patterns in this definition are not exhaustive\nunmatched patterns:",
            );
            for pat in args_exhaustion.unmatched_patterns {
                message += &format!("\n    {} {}", def_ident.name, pat);
            }
            messages.push(ErrorMessage::new(
                message,
                Severity::Error,
                Diagnostic::at(self.source_file, &def_ident.range),
            ))
        }

        DiagnosticResult::ok_with_many((), messages)
    }

    /// Converts a pattern representing a function invocation into a pattern object.
    /// The returned values are the function's parameters.
    /// This function does not guarantee that the returned pattern is valid for the function.
    fn resolve_func_pattern(
        &self,
        function_name: &str,
        expression: ExprPatP,
    ) -> DiagnosticResult<Vec<Pattern>> {
        match expression {
            ExprPatP::Variable(identifier) => {
                // This identifier should be the function.
                let symbol = resolve_definition(self.source_file, &identifier, self.project_index);
                symbol.bind(|(symbol_source_file, symbol)| {
                    // Verify that the symbol really is the function.
                    if symbol_source_file != self.source_file || symbol.name.name != function_name {
                        DiagnosticResult::fail(ErrorMessage::new_with(
                            String::from("this did not match the function being defined"),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &identifier),
                            HelpMessage {
                                message: format!("replace this with `{}`", function_name),
                                help_type: HelpType::Help,
                                diagnostic: Diagnostic::at(self.source_file, &identifier),
                            },
                        ))
                    } else {
                        DiagnosticResult::ok(Vec::new())
                    }
                })
            }
            ExprPatP::Apply(left, right) => {
                // The left hand side should be a function pattern, and the right hand side should be a type pattern.
                self.resolve_func_pattern(function_name, *left)
                    .bind(|mut left| {
                        self.resolve_type_pattern(*right).map(|right| {
                            left.push(right);
                            left
                        })
                    })
            }
            ExprPatP::Unknown(range) => {
                // This is invalid, the function must be the pattern.
                DiagnosticResult::fail(ErrorMessage::new_with(
                    String::from("this did not match the function being defined"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                    HelpMessage {
                        message: format!("replace this with `{}`", function_name),
                        help_type: HelpType::Help,
                        diagnostic: Diagnostic::at(self.source_file, &range),
                    },
                ))
            }
            ExprPatP::Lambda { lambda_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("lambda abstractions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &lambda_token),
            )),
            ExprPatP::Let { let_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("let expressions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &let_token),
            )),
            ExprPatP::Block { open_bracket, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("blocks are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &open_bracket),
            )),
            ExprPatP::ConstructData {
                data_constructor, ..
            } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("data constructors are not allowed in function patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &data_constructor),
            )),
        }
    }

    /// Converts a pattern representing a type constructor into a pattern object.
    fn resolve_type_pattern(&self, expression: ExprPatP) -> DiagnosticResult<Pattern> {
        match expression {
            ExprPatP::Variable(identifier) => {
                if identifier.segments.len() == 1 {
                    DiagnosticResult::ok(Pattern::Named(NameP {
                        name: identifier.segments[0].name.clone(),
                        range: identifier.range(),
                    }))
                } else {
                    DiagnosticResult::fail(ErrorMessage::new(
                        "expected a variable name, not a qualified name".to_string(),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &identifier),
                    ))
                }
            }
            ExprPatP::Apply(left, _right) => DiagnosticResult::fail(ErrorMessage::new(
                String::from("expected a type constructor pattern"),
                Severity::Error,
                Diagnostic::at(self.source_file, &*left),
            )),
            ExprPatP::Unknown(range) => DiagnosticResult::ok(Pattern::Unknown(range)),
            ExprPatP::Lambda { lambda_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("lambda abstractions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &lambda_token),
            )),
            ExprPatP::Let { let_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("let expressions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &let_token),
            )),
            ExprPatP::Block { open_bracket, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("blocks are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &open_bracket),
            )),
            ExprPatP::ConstructData {
                data_constructor,
                fields,
                ..
            } => {
                let fields = fields
                    .fields
                    .into_iter()
                    .map(|(field_name, field_pattern)| {
                        self.resolve_type_pattern(field_pattern)
                            .map(|pat| (field_name, pat))
                    })
                    .chain(fields.auto_fields.into_iter().map(|field_name| {
                        DiagnosticResult::ok((field_name.clone(), Pattern::Named(field_name)))
                    }))
                    .collect::<DiagnosticResult<_>>();
                fields.bind(|fields| {
                    resolve_type_constructor(
                        self.source_file,
                        &data_constructor,
                        self.project_index,
                    )
                    .map(|type_ctor| Pattern::TypeConstructor { type_ctor, fields })
                })
            }
        }
    }
}

/// Flattens a list of maps into a single map, adding error messages if variables were multiply defined.
fn collect_bound_vars(
    source_file: &SourceFileIdentifier,
    bound_variables: Vec<HashMap<String, BoundVariable>>,
) -> DiagnosticResult<HashMap<String, BoundVariable>> {
    let mut messages = Vec::new();
    let mut map = HashMap::<String, BoundVariable>::new();

    for inner in bound_variables {
        for (k, v) in inner {
            match map.entry(k) {
                Entry::Occupied(occupied) => {
                    messages.push(ErrorMessage::new_with(
                        format!("variable `{}` was already defined", occupied.key()),
                        Severity::Error,
                        Diagnostic::at(source_file, &v.range),
                        HelpMessage {
                            message: String::from("previously defined here"),
                            help_type: HelpType::Note,
                            diagnostic: Diagnostic::at(source_file, &occupied.get().range),
                        },
                    ));
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(v);
                }
            }
        }
    }

    DiagnosticResult::ok_with_many(map, messages)
}

/// Treating this symbol as a function, what are its arguments' types and the result type?
/// If this is not a function, then it is treated as a zero-argument function.
fn get_args_of_type(symbol_type: &Type) -> (Vec<Type>, Type) {
    match symbol_type {
        Type::Named { .. } => (Vec::new(), symbol_type.clone()),
        Type::Function(left, right) => {
            let (mut args, out) = get_args_of_type(&right);
            args.insert(0, *left.clone());
            (args, out)
        }
        Type::Variable { .. } => (Vec::new(), symbol_type.clone()),
    }
}

/// Treating this symbol as a function, what are its arguments' types and the result type?
/// If this is not a function, then it is treated as a zero-argument function.
///
/// This enforces that the function is treated as a `num_args`-argument function,
/// by currying arguments until the required arity is achieved.
fn get_args_of_type_arity(symbol_type: &Type, num_args: usize) -> (Vec<Type>, Type) {
    let (mut symbol_args, mut result) = get_args_of_type(symbol_type);

    // Now, let's edit the `symbol_args` and `result` type to match the number of arguments we supplied.
    // For example, if we have a function of type `a -> b -> c` and we supplied one argument of type `a`, the result is of type `b -> c`.
    while symbol_args.len() > num_args {
        let last_arg = symbol_args.pop().unwrap();
        result = Type::Function(Box::new(last_arg), Box::new(result));
    }

    (symbol_args, result)
}
