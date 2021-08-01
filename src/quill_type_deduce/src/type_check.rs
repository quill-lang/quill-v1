//! Performs type deduction and type checking of expressions and patterns.

use std::collections::{btree_map::Entry, BTreeMap};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::{
    compute_used_files, AspectI, DefinitionI, ProjectIndex, TypeDeclarationI, TypeDeclarationTypeI,
    TypeParameter,
};
use quill_parser::{
    definition::{DefinitionBodyP, DefinitionCaseP, DefinitionDeclP, DefinitionP, TypeParameterP},
    expr_pat::{ConstantValue, ConstructDataFields, ExprPatP},
    file::FileP,
    identifier::{IdentifierP, NameP},
    types::TypeP,
    visibility::Visibility,
};
use quill_type::{BorrowCondition, PrimitiveType, Type};

use crate::{
    hindley_milner::deduce_expr_type,
    hir::{
        definition::{Definition, DefinitionBody, DefinitionCase},
        expr::{BoundVariable, Expression, ExpressionContents, TypeVariable},
        pattern::Pattern,
        SourceFileHIR,
    },
    index_resolve::{replace_type_variables, resolve_type_constructor},
    type_resolve::TypeVariableId,
};

pub fn check(
    source_file: &SourceFileIdentifier,
    project_index: &ProjectIndex,
    file_parsed: FileP,
) -> DiagnosticResult<SourceFileHIR> {
    let type_checker = TypeChecker {
        source_file,
        project_index,
        messages: Vec::new(),
    };
    type_checker.compute(project_index, file_parsed)
}

pub(crate) struct TypeChecker<'a> {
    pub(crate) source_file: &'a SourceFileIdentifier,
    pub(crate) project_index: &'a ProjectIndex,

    pub(crate) messages: Vec<ErrorMessage>,
}

/// A utility for printing type variables to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct TypeVariablePrinter {
    /// Maps type variable IDs to the names we use to render them.
    type_variable_names: BTreeMap<TypeVariableId, String>,
    /// When we see a new type variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    type_variable_name: u32,
    /// A substitution mapping type variables to the substituted type variable.
    /// This map is tried before making a new name for a type variable.
    substitution: BTreeMap<TypeVariableId, TypeVariable>,
}

impl TypeVariablePrinter {
    pub fn new(substitution: BTreeMap<TypeVariableId, TypeVariable>) -> Self {
        Self {
            type_variable_names: BTreeMap::new(),
            type_variable_name: 0,
            substitution,
        }
    }

    pub fn print(&mut self, ty: TypeVariable) -> String {
        match ty {
            TypeVariable::Named { name, parameters } => {
                let mut result = name.to_string();
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
            TypeVariable::Primitive(prim) => format!("{}", prim),
            TypeVariable::Borrow { ty } => {
                format!("&{}", self.print(*ty))
            }
            TypeVariable::Impl { name, parameters } => {
                let mut result = format!("impl {}", name);
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
        if let Some(result) = self.type_variable_names.get(ty) {
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

/// Represents a declaration that may be in a different source file.
pub struct ForeignDeclaration<T> {
    pub source_file: SourceFileIdentifier,
    pub decl: T,
}

pub struct VisibleNames<'a> {
    pub types: BTreeMap<&'a str, ForeignDeclaration<&'a TypeDeclarationI>>,
    pub enum_variants: BTreeMap<&'a str, ForeignDeclaration<&'a str>>,
    pub definitions: BTreeMap<&'a str, ForeignDeclaration<&'a DefinitionI>>,
    pub aspects: BTreeMap<&'a str, ForeignDeclaration<&'a AspectI>>,
}

/// Work out what names are visible inside a file.
/// This is the counterpart to `compute_visible_types_and_aspects` once we've got the full project index.
fn compute_visible_names<'a>(
    source_file: &'a SourceFileIdentifier,
    file_parsed: &FileP,
    project_index: &'a ProjectIndex,
) -> DiagnosticResult<VisibleNames<'a>> {
    let mut messages = Vec::new();
    let mut visible_types = BTreeMap::<&str, Vec<ForeignDeclaration<_>>>::new();
    let mut visible_enum_variants = BTreeMap::<&str, Vec<ForeignDeclaration<_>>>::new();
    let mut visible_defs = BTreeMap::<&str, Vec<ForeignDeclaration<_>>>::new();
    let mut visible_aspects = BTreeMap::<&str, Vec<ForeignDeclaration<_>>>::new();

    let (used_files, more_messages) = compute_used_files(source_file, file_parsed, |name| {
        project_index.contains_key(name)
    })
    .destructure();
    assert!(
        more_messages.is_empty(),
        "should have errored in `compute_visible_types_and_aspects`"
    );
    for file in used_files.unwrap() {
        let file_index = &project_index[&file.file];
        for (ty, decl) in &file_index.types {
            visible_types
                .entry(ty.as_str())
                .or_default()
                .push(ForeignDeclaration {
                    source_file: file.file.clone(),
                    decl,
                });
        }
        for (variant, ty) in &file_index.enum_variant_types {
            visible_enum_variants
                .entry(variant.as_str())
                .or_default()
                .push(ForeignDeclaration {
                    source_file: file.file.clone(),
                    decl: &file_index.types[ty],
                });
        }
        for (name, def) in &file_index.definitions {
            visible_defs
                .entry(name.as_str())
                .or_default()
                .push(ForeignDeclaration {
                    source_file: file.file.clone(),
                    decl: def,
                });
        }
        for (name, def) in &file_index.aspects {
            visible_aspects
                .entry(name.as_str())
                .or_default()
                .push(ForeignDeclaration {
                    source_file: file.file.clone(),
                    decl: def,
                });
        }
    }

    // Now generate error messages if the multimap contains any duplicate entries.
    let types = visible_types
        .into_iter()
        .map(|(key, mut decls)| {
            if decls.len() == 1 {
                (key, decls.pop().unwrap())
            } else {
                unreachable!("should have errored in `compute_visible_types`")
            }
        })
        .collect();
    let enum_variants = visible_enum_variants.into_iter().filter_map(|(key, mut decls)| {
        if decls.len() == 1 {
            let decl = decls.pop().unwrap();
            Some((key, ForeignDeclaration { source_file: decl.source_file, decl: decl.decl.name.name.as_str() }))
        } else {
            messages.push(ErrorMessage::new_with_many(
                format!("an enum variant with name `{}` was imported from multiple locations, which could cause ambiguity, so this name will not be usable in this file", key),
                Severity::Warning,
                Diagnostic::in_file(source_file),
                decls.into_iter().map(|decl| HelpMessage {
                    message: format!("defined in {} here", decl.source_file),
                    help_type: HelpType::Note,
                    diagnostic: Diagnostic::at(&decl.source_file, &decl.decl.name.range),
                }).collect()
            ));
            None
        }
    })
        .collect();
    let definitions = visible_defs.into_iter().filter_map(|(key, mut decls)| {
        if decls.len() == 1 {
            Some((key, decls.pop().unwrap()))
        } else {
            messages.push(ErrorMessage::new_with_many(
                format!("a definition with name `{}` was imported from multiple locations, which could cause ambiguity, so this name will not be usable in this file", key),
                Severity::Warning,
                Diagnostic::in_file(source_file),
                decls.into_iter().map(|decl| HelpMessage {
                    message: format!("defined in {} here", decl.source_file),
                    help_type: HelpType::Note,
                    diagnostic: Diagnostic::at(&decl.source_file, &decl.decl.name.range),
                }).collect()
            ));
            None
        }
    })
        .collect();
    let aspects = visible_aspects.into_iter().filter_map(|(key, mut decls)| {
            if decls.len() == 1 {
                Some((key, decls.pop().unwrap()))
            } else {
                messages.push(ErrorMessage::new_with_many(
                    format!("an aspect with name `{}` was imported from multiple locations, which could cause ambiguity, so this name will not be usable in this file", key),
                    Severity::Warning,
                    Diagnostic::in_file(source_file),
                    decls.into_iter().map(|decl| HelpMessage {
                        message: format!("defined in {} here", decl.source_file),
                        help_type: HelpType::Note,
                        diagnostic: Diagnostic::at(&decl.source_file, &decl.decl.name.range),
                    }).collect()
                ));
                None
            }
        })
            .collect();

    DiagnosticResult::ok_with_many(
        VisibleNames {
            types,
            enum_variants,
            definitions,
            aspects,
        },
        messages,
    )
}

impl<'a> TypeChecker<'a> {
    fn compute(
        mut self,
        project_index: &ProjectIndex,
        file_parsed: FileP,
    ) -> DiagnosticResult<SourceFileHIR> {
        let visible_names = {
            let (visible_names, more_messages) =
                compute_visible_names(self.source_file, &file_parsed, project_index).destructure();
            self.messages.extend(more_messages);
            visible_names.unwrap()
        };

        let mut definitions = BTreeMap::<String, Definition>::new();

        for definition in file_parsed.definitions {
            let symbol =
                &self.project_index[self.source_file].definitions[&definition.decl.name.name];
            let symbol_type = &symbol.symbol_type;

            if let Some((name, def)) =
                self.compute_definition(&visible_names, definition, symbol_type)
            {
                definitions.insert(name, def);
            }
        }

        DiagnosticResult::ok_with_many(SourceFileHIR { definitions }, self.messages)
    }

    /// Returns a string for the definition name, along with the fully type checked definition.
    /// Appends messages to the inner message log.
    fn compute_definition(
        &mut self,
        visible_names: &VisibleNames,
        definition: DefinitionP,
        symbol_type: &Type,
    ) -> Option<(String, Definition)> {
        let def_name = definition.decl.name;
        let type_parameters = definition.decl.type_parameters;
        match definition.body {
            DefinitionBodyP::PatternMatch(cases) => {
                // We need to check pattern exhaustiveness in the definition's cases.
                // Let's resolve each case's patterns and expressions.
                let cases = cases
                    .into_iter()
                    .map(|case| {
                        self.resolve_case(visible_names, &def_name.name, case, symbol_type.clone())
                    })
                    .collect::<DiagnosticResult<_>>();

                // Now we can check whether the patterns are valid.
                let cases_validated = cases.bind(|cases| {
                    cases
                        .into_iter()
                        .map(|(range, args, replacement)| {
                            self.validate_case(
                                visible_names,
                                symbol_type,
                                range,
                                args,
                                replacement,
                                def_name.range,
                            )
                        })
                        .collect::<DiagnosticResult<_>>()
                });
                // Check that the patterns we have generated are exhaustive.
                let validated = cases_validated.deny().map(|cases_validated| {
                    let arity = cases_validated[0].1.len();
                    (cases_validated, arity)
                });

                let (definition_parsed, mut inner_messages) = validated.destructure();
                self.messages.append(&mut inner_messages);
                if let Some((cases, arity)) = definition_parsed {
                    let (arg_types, return_type) = get_args_of_type_arity(symbol_type, arity);

                    let def = Definition {
                        range: def_name.range,
                        type_variables: type_parameters
                            .into_iter()
                            .map(|id| TypeParameter {
                                name: id.name.name,
                                parameters: id.parameters,
                            })
                            .collect(),
                        arg_types,
                        return_type,
                        body: DefinitionBody::PatternMatch(
                            cases
                                .into_iter()
                                .map(|(range, arg_patterns, replacement)| DefinitionCase {
                                    range,
                                    arg_patterns,
                                    replacement,
                                })
                                .collect(),
                        ),
                    };

                    Some((def_name.name, def))
                } else {
                    None
                }
            }
            DefinitionBodyP::CompilerIntrinsic(_) => {
                // There's no type checking to be done for a compiler intrinsic.
                // All compiler intrinsics have the maximal possible arity.
                let (arg_types, return_type) = get_args_of_type(symbol_type);

                let def = Definition {
                    range: def_name.range,
                    type_variables: type_parameters
                        .into_iter()
                        .map(|id| TypeParameter {
                            name: id.name.name,
                            parameters: id.parameters,
                        })
                        .collect(),
                    arg_types,
                    return_type,
                    body: DefinitionBody::CompilerIntrinsic,
                };

                Some((def_name.name, def))
            }
        }
    }

    fn resolve_case(
        &self,
        visible_names: &VisibleNames,
        function_name: &str,
        case: DefinitionCaseP,
        symbol_type: Type,
    ) -> DiagnosticResult<(Range, Vec<Pattern>, ExprPatP)> {
        let range = case.pattern.range();
        let pattern =
            self.resolve_func_pattern(visible_names, function_name, case.pattern, symbol_type);
        let replacement = case.replacement;
        pattern.map(|pattern| (range, pattern, replacement))
    }

    /// Verify that the given case exactly matches the required type, and also type check the expression given the arguments' types and the expected output type.
    fn validate_case(
        &self,
        visible_names: &VisibleNames,
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
            .map(|(pattern, expected_type)| {
                self.match_and_bind(visible_names, pattern, expected_type, None)
            })
            .collect::<DiagnosticResult<_>>();
        // Collect the list of maps into a single map, ensuring that we don't have duplicate variable names.
        let arg_vars = arg_vars.bind(|arg_vars| collect_bound_vars(self.source_file, arg_vars));

        // Now, parse the expression, now that we know the input variable types.
        arg_vars
            .bind(|arg_vars| {
                deduce_expr_type(
                    self.source_file,
                    self.project_index,
                    visible_names,
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
    /// If `borrow_condition` is Some, then this is inside a borrow with the given condition.
    /// Under this circumstance, the returned type should instead be a borrowed type.
    fn match_and_bind(
        &self,
        visible_names: &VisibleNames,
        pattern: &Pattern,
        expected_type: Type,
        borrow_condition: Option<BorrowCondition>,
    ) -> DiagnosticResult<BTreeMap<String, BoundVariable>> {
        match pattern {
            Pattern::Named(identifier) => {
                let mut map = BTreeMap::new();
                map.insert(
                    identifier.name.clone(),
                    BoundVariable {
                        var_type: if let Some(borrow_condition) = borrow_condition {
                            Type::Borrow {
                                ty: Box::new(expected_type),
                                borrow: Some(borrow_condition),
                            }
                        } else {
                            expected_type
                        },
                        range: identifier.range,
                    },
                );
                DiagnosticResult::ok(map)
            }
            Pattern::Constant { .. } => DiagnosticResult::ok(BTreeMap::new()),
            Pattern::TypeConstructor {
                type_ctor,
                fields: provided_fields,
            } => match expected_type {
                Type::Named {
                    parameters: concrete_type_parameters,
                    ..
                } => {
                    // Find the data type declaration in the index.
                    let data_type_decl =
                        visible_names.types[type_ctor.data_type.name.as_str()].decl;
                    // Find the original list of named type parameters.
                    // For instance, in a data type `Foo[A]`, the named type parameter list is `[A]`.
                    // We can then create a bijective correspondence between the list of `concrete_type_parameters` given
                    // and the list of `named_type_parameters`, so we can identify which type parameter has which value.
                    // Also, find the list of fields for the type constructor that we're creating.
                    let (named_type_parameters, expected_fields) = {
                        match &data_type_decl.decl_type {
                            TypeDeclarationTypeI::Data(datai) => {
                                let fields = datai
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .map(|(name, ty)| (name.name.clone(), ty.clone()))
                                    .collect::<BTreeMap<String, Type>>();
                                (&datai.type_params, fields)
                            }
                            TypeDeclarationTypeI::Enum(enumi) => {
                                let variant = enumi
                                    .variants
                                    .iter()
                                    .find(|variant| {
                                        &variant.name.name == type_ctor.variant.as_ref().unwrap()
                                    })
                                    .unwrap();
                                let fields = variant
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .map(|(name, ty)| (name.name.clone(), ty.clone()))
                                    .collect::<BTreeMap<String, Type>>();
                                (&enumi.type_params, fields)
                            }
                        }
                    };

                    // Process the fields provided to this type constructor.
                    let provided_fields = provided_fields
                        .iter()
                        .map(|(name, _ty, pat)| (name.name.clone(), pat.clone()))
                        .collect::<BTreeMap<String, Pattern>>();

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
                            bound_vars.push(self.match_and_bind(
                                visible_names,
                                pattern,
                                expected_type,
                                borrow_condition.clone(),
                            ));
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
                }
                _ => panic!("should have errored in resolve_type_pattern"),
            },
            Pattern::Impl {
                impl_token,
                fields: provided_fields,
                ..
            } => match expected_type {
                Type::Impl {
                    name: aspect_name,
                    parameters: concrete_type_parameters,
                    ..
                } => {
                    // Find the data type declaration in the index.
                    let decl = &visible_names.aspects[aspect_name.name.as_str()];

                    // Find the original list of named type parameters.
                    // For instance, in a data type `Foo[A]`, the named type parameter list is `[A]`.
                    // We can then create a bijective correspondence between the list of `concrete_type_parameters` given
                    // and the list of `named_type_parameters`, so we can identify which type parameter has which value.
                    // Also, find the list of fields for the type constructor that we're creating.
                    let (named_type_parameters, expected_fields) = {
                        let fields = decl
                            .decl
                            .definitions
                            .iter()
                            .map(|def| (def.name.name.clone(), def.symbol_type.clone()))
                            .collect::<BTreeMap<String, Type>>();
                        (&decl.decl.type_variables, fields)
                    };

                    // Process the fields provided to this type constructor.
                    let provided_fields = provided_fields
                        .iter()
                        .map(|(name, _ty, pat)| (name.name.clone(), pat.clone()))
                        .collect::<BTreeMap<String, Pattern>>();

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
                            bound_vars.push(self.match_and_bind(
                                visible_names,
                                pattern,
                                expected_type,
                                borrow_condition.clone(),
                            ));
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
                                        Diagnostic::at(self.source_file, impl_token),
                                    ))
                                }
                            }
                            DiagnosticResult::ok_with_many(result, messages)
                        })
                }
                _ => panic!("should have errored in resolve_type_pattern"),
            },
            Pattern::Borrow { borrowed, .. } => {
                match expected_type {
                    Type::Borrow { ty, borrow } => {
                        // Add the lifetime to the types inside this borrow.
                        // The `Some(borrow.unwrap())` asserts that `borrow` is Some.
                        self.match_and_bind(visible_names, &*borrowed, *ty, Some(borrow.unwrap()))
                    }
                    _ => panic!("should have errored in resolve_type_pattern"),
                }
            }
            Pattern::Unknown(_) => DiagnosticResult::ok(BTreeMap::new()),
            Pattern::Function { .. } => unimplemented!(),
        }
    }

    /// Converts a pattern representing a function invocation into a pattern object.
    /// The returned values are the function's parameters.
    /// This function does not guarantee that the returned pattern is valid for the function.
    fn resolve_func_pattern(
        &self,
        visible_names: &VisibleNames,
        function_name: &str,
        expression: ExprPatP,
        symbol_type: Type,
    ) -> DiagnosticResult<Vec<Pattern>> {
        // We decompose the pattern into the name of the function followed by its arguments.
        let mut args = Vec::new();
        let mut function_name_expr = expression;
        while let ExprPatP::Apply(left, right) = function_name_expr {
            function_name_expr = *left;
            args.insert(0, *right);
        }

        if let ExprPatP::Variable(identifier) = function_name_expr {
            // This identifier should be the function.
            if identifier.segments.len() == 1 && identifier.segments[0].name == function_name {
            } else {
                return DiagnosticResult::fail(ErrorMessage::new_with(
                    String::from("this did not match the function being defined"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &identifier),
                    HelpMessage {
                        message: format!("replace this with `{}`", function_name),
                        help_type: HelpType::Help,
                        diagnostic: Diagnostic::at(self.source_file, &identifier),
                    },
                ));
            }
        } else {
            return DiagnosticResult::fail(ErrorMessage::new_with(
                String::from("expected the name of the function"),
                Severity::Error,
                Diagnostic::at(self.source_file, &function_name_expr),
                HelpMessage {
                    message: format!("replace this with `{}`", function_name),
                    help_type: HelpType::Help,
                    diagnostic: Diagnostic::at(self.source_file, &function_name_expr),
                },
            ));
        }

        // Check that the amount of arguments is at most the arity of this function.
        // This is done by first finding the maximal list of arguments to be supplied to this function.
        let (param_types, _return_type) = get_args_of_type(&symbol_type);

        if param_types.len() < args.len() {
            return DiagnosticResult::fail(ErrorMessage::new_with(
                String::from("too many arguments"),
                Severity::Error,
                Diagnostic::at(
                    self.source_file,
                    &args[param_types.len()..]
                        .iter()
                        .map(|arg| arg.range())
                        .reduce(Range::union)
                        .unwrap(),
                ),
                HelpMessage {
                    message: "remove this extra argument".to_string(),
                    help_type: HelpType::Help,
                    diagnostic: Diagnostic::at(self.source_file, &args[param_types.len()]),
                },
            ));
        }

        // Now that the function's name has been parsed, let's process each argument.
        args.into_iter()
            .zip(param_types)
            .map(|(expression, ty)| self.resolve_type_pattern(visible_names, expression, ty))
            .collect::<DiagnosticResult<Vec<_>>>()
    }

    /// Converts a pattern representing a value or type constructor into a pattern object.
    /// We know ahead of time what type this value should be, but we have no guarantee that the given
    /// pattern really matches this type. If a type mismatch is found, an error is emitted.
    pub(crate) fn resolve_type_pattern(
        &self,
        visible_names: &VisibleNames,
        expression: ExprPatP,
        expected_type: Type,
    ) -> DiagnosticResult<Pattern> {
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
            ExprPatP::Constant { range, value } => match expected_type {
                Type::Borrow { ty, .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected a borrow of a value of type {}, not `{}`",
                        ty,
                        get_constant_type(&value)
                    ),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                )),
                Type::Named { .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected a type constructor, not `{}`",
                        get_constant_type(&value)
                    ),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                )),
                Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                    format!("expected a function, not `{}`", get_constant_type(&value)),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                )),
                Type::Variable { variable, .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected a value of type `{}`, not `{}`",
                        variable,
                        get_constant_type(&value)
                    ),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                )),
                Type::Primitive(prim) => {
                    // We need to check that the expected type and the value's type are the same.
                    if prim == get_constant_type(&value) {
                        DiagnosticResult::ok(Pattern::Constant { range, value })
                    } else {
                        DiagnosticResult::fail(ErrorMessage::new(
                            format!(
                                "expected a value of type `{}`, not `{}`",
                                prim,
                                get_constant_type(&value)
                            ),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &range),
                        ))
                    }
                }
                Type::Impl { .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!(
                        "expected an aspect implementation, not `{}`",
                        get_constant_type(&value),
                    ),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &range),
                )),
            },
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
            ExprPatP::Borrow {
                borrow_token, expr, ..
            } => match expected_type {
                Type::Borrow { ty, .. } => self
                    .resolve_type_pattern(visible_names, *expr, *ty)
                    .map(|pat| Pattern::Borrow {
                        borrow_token,
                        borrowed: Box::new(pat),
                    }),
                Type::Named { .. } => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected a type constructor, not a borrow"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &borrow_token),
                )),
                Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected a function, not a borrow"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &borrow_token),
                )),
                Type::Variable { variable, .. } => DiagnosticResult::fail(ErrorMessage::new(
                    format!("expected a value of type `{}`, not a borrow", variable),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &borrow_token),
                )),
                Type::Primitive(prim) => DiagnosticResult::fail(ErrorMessage::new(
                    format!("expected a value of type {}, not a borrow", prim),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &borrow_token),
                )),
                Type::Impl { .. } => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("expected an aspect implementation, not a borrow"),
                    Severity::Error,
                    Diagnostic::at(self.source_file, &borrow_token),
                )),
            },
            ExprPatP::Copy { copy_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("copies are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &copy_token),
            )),
            ExprPatP::ConstructData {
                data_constructor,
                fields,
                ..
            } => resolve_type_constructor(self.source_file, &data_constructor, visible_names).bind(
                |type_ctor| {
                    match expected_type {
                        Type::Named { name, parameters } => {
                            let field_types = match &self.project_index[&name.source_file].types
                                [&name.name]
                                .decl_type
                            {
                                TypeDeclarationTypeI::Data(datai) => datai
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .map(|(name, ty)| {
                                        (
                                            name,
                                            replace_type_variables(
                                                ty.clone(),
                                                &datai.type_params,
                                                &parameters,
                                            ),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                                TypeDeclarationTypeI::Enum(enumi) => enumi
                                    .variants
                                    .iter()
                                    .find(|variant| {
                                        variant.name.name == type_ctor.variant.as_deref().unwrap()
                                    })
                                    .unwrap() // FIXME: this can panic if an enum variant for the wrong enum is supplied
                                    .type_ctor
                                    .fields
                                    .iter()
                                    .map(|(name, ty)| {
                                        (
                                            name,
                                            replace_type_variables(
                                                ty.clone(),
                                                &enumi.type_params,
                                                &parameters,
                                            ),
                                        )
                                    })
                                    .collect::<Vec<_>>(),
                            };

                            let fields =
                                self.resolve_destructure(visible_names, fields, &field_types);

                            fields.map(|fields| {
                                // Find the fields on the type, and cache their types.
                                Pattern::TypeConstructor {
                                    type_ctor,
                                    fields: fields
                                        .into_iter()
                                        .map(|(name, pat)| {
                                            let ty = field_types
                                                .iter()
                                                .find_map(|(fname, ftype)| {
                                                    if **fname == name {
                                                        Some(ftype.clone())
                                                    } else {
                                                        None
                                                    }
                                                })
                                                .unwrap();
                                            (name, ty, pat)
                                        })
                                        .collect(),
                                }
                            })
                        }
                        Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                            String::from("expected a function, not a type constructor"),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &type_ctor.range),
                        )),
                        Type::Variable { variable, .. } => {
                            DiagnosticResult::fail(ErrorMessage::new(
                                format!(
                                    "expected a value of type `{}`, not a type constructor",
                                    variable
                                ),
                                Severity::Error,
                                Diagnostic::at(self.source_file, &type_ctor.range),
                            ))
                        }
                        Type::Primitive(prim) => DiagnosticResult::fail(ErrorMessage::new(
                            format!("expected a value of type {}, not a type constructor", prim),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &type_ctor.range),
                        )),
                        Type::Borrow { ty, .. } => DiagnosticResult::fail(ErrorMessage::new(
                            format!(
                                "expected a borrow of a value of type {}, not a type constructor",
                                ty
                            ),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &type_ctor.range),
                        )),
                        Type::Impl { .. } => DiagnosticResult::fail(ErrorMessage::new(
                            String::from(
                                "expected an aspect implementation, not a type constructor",
                            ),
                            Severity::Error,
                            Diagnostic::at(self.source_file, &type_ctor.range),
                        )),
                    }
                },
            ),
            ExprPatP::Impl { .. } => unreachable!(),
            ExprPatP::ImplPattern {
                impl_token, fields, ..
            } => {
                match &expected_type {
                    Type::Impl { name, parameters } => {
                        let aspecti = &self.project_index[&name.source_file].aspects[&name.name];
                        let field_types = aspecti
                            .definitions
                            .iter()
                            .map(|def| {
                                (
                                    &def.name,
                                    replace_type_variables(
                                        def.symbol_type.clone(),
                                        &aspecti.type_variables,
                                        parameters,
                                    ),
                                )
                            })
                            .collect::<Vec<_>>();

                        let fields = self.resolve_destructure(visible_names, fields, &field_types);

                        fields.map(|fields| {
                            // Find the fields on the type, and cache their types.
                            Pattern::Impl {
                                impl_token,
                                fields: fields
                                    .into_iter()
                                    .map(|(name, pat)| {
                                        let ty = field_types
                                            .iter()
                                            .find_map(|(fname, ftype)| {
                                                if **fname == name {
                                                    Some(ftype.clone())
                                                } else {
                                                    None
                                                }
                                            })
                                            .unwrap();
                                        (name, ty, pat)
                                    })
                                    .collect(),
                            }
                        })
                    }
                    Type::Named { .. } => DiagnosticResult::fail(ErrorMessage::new(
                        String::from("expected a type constructor, not an impl"),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &impl_token),
                    )),
                    Type::Function(_, _) => DiagnosticResult::fail(ErrorMessage::new(
                        String::from("expected a function, not an impl"),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &impl_token),
                    )),
                    Type::Variable { variable, .. } => DiagnosticResult::fail(ErrorMessage::new(
                        format!("expected a value of type `{}`, not an impl", variable),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &impl_token),
                    )),
                    Type::Primitive(prim) => DiagnosticResult::fail(ErrorMessage::new(
                        format!("expected a value of type {}, not an impl", prim),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &impl_token),
                    )),
                    Type::Borrow { ty, .. } => DiagnosticResult::fail(ErrorMessage::new(
                        format!("expected a borrow of a value of type {}, not an impl", ty),
                        Severity::Error,
                        Diagnostic::at(self.source_file, &impl_token),
                    )),
                }
            }
            ExprPatP::Match { match_token, .. } => DiagnosticResult::fail(ErrorMessage::new(
                String::from("match expressions are not allowed in patterns"),
                Severity::Error,
                Diagnostic::at(self.source_file, &match_token),
            )),
        }
    }

    fn resolve_destructure(
        &self,
        visible_names: &VisibleNames,
        fields: ConstructDataFields,
        field_types: &[(&NameP, Type)],
    ) -> DiagnosticResult<Vec<(NameP, Pattern)>> {
        // Use the known types of each fields to find the real types of each field
        // in this destructure block.
        fields
            .fields
            .into_iter()
            .map(|(field_name, field_pattern)| {
                self.resolve_type_pattern(
                    visible_names,
                    field_pattern,
                    field_types
                        .iter()
                        .find_map(
                            |(name, ty)| {
                                if **name == field_name {
                                    Some(ty)
                                } else {
                                    None
                                }
                            },
                        )
                        .unwrap()
                        .clone(),
                )
                .map(|pat| (field_name, pat))
            })
            .chain(fields.auto_fields.into_iter().map(|field_name| {
                DiagnosticResult::ok((field_name.clone(), Pattern::Named(field_name)))
            }))
            .collect::<DiagnosticResult<_>>()
    }

    /// Type check the implementation of an aspect.
    pub(crate) fn compute_impl(
        mut self,
        impl_token: Range,
        aspect: &AspectI,
        parameters: &[Type],
        cases: Vec<DefinitionCaseP>,
        visible_names: &VisibleNames,
    ) -> DiagnosticResult<ExpressionContents> {
        // Split apart each definition in the impl body.
        let mut cases_by_func_name = BTreeMap::<String, Vec<DefinitionCaseP>>::new();
        for case in cases {
            let func_name = get_func_name(&case.pattern);
            cases_by_func_name.entry(func_name).or_default().push(case);
        }

        let mut implementations = BTreeMap::new();

        for def in &aspect.definitions {
            let symbol_type =
                replace_type_variables(def.symbol_type.clone(), &aspect.type_variables, parameters);

            let implementation = DefinitionP {
                decl: DefinitionDeclP {
                    vis: Visibility::Private,
                    name: NameP {
                        name: def.name.name.clone(),
                        range: impl_token,
                    },
                    type_parameters: def
                        .type_variables
                        .iter()
                        .map(|param| TypeParameterP {
                            name: NameP {
                                name: param.name.clone(),
                                range: impl_token,
                            },
                            parameters: param.parameters,
                        })
                        .collect(),
                    definition_type: to_typep(&symbol_type, impl_token),
                },
                body: DefinitionBodyP::PatternMatch(
                    cases_by_func_name
                        .remove(&def.name.name)
                        .unwrap_or_default(),
                ),
            };

            // Type check this implementation.
            let result = self.compute_definition(visible_names, implementation, &symbol_type);
            if let Some((k, v)) = result {
                implementations.insert(k, v);
            }
        }

        DiagnosticResult::ok_with_many(
            ExpressionContents::Impl {
                impl_token,
                implementations,
            },
            std::mem::take(&mut self.messages),
        )
    }
}

fn get_constant_type(constant: &ConstantValue) -> PrimitiveType {
    match constant {
        ConstantValue::Unit => PrimitiveType::Unit,
        ConstantValue::Bool(_) => PrimitiveType::Bool,
        ConstantValue::Int(_) => PrimitiveType::Int,
    }
}

/// Retrieves the function name defined by this function pattern.
fn get_func_name(pattern: &ExprPatP) -> String {
    match pattern {
        ExprPatP::Variable(name) => name.segments[0].name.clone(),
        ExprPatP::Apply(left, _) => get_func_name(&*left),
        _ => unreachable!(),
    }
}

/// Flattens a list of maps into a single map, adding error messages if variables were multiply defined.
fn collect_bound_vars(
    source_file: &SourceFileIdentifier,
    bound_variables: Vec<BTreeMap<String, BoundVariable>>,
) -> DiagnosticResult<BTreeMap<String, BoundVariable>> {
    let mut messages = Vec::new();
    let mut map = BTreeMap::<String, BoundVariable>::new();

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
        Type::Function(left, right) => {
            let (mut args, out) = get_args_of_type(right);
            args.insert(0, *left.clone());
            (args, out)
        }
        _ => (Vec::new(), symbol_type.clone()),
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

/// A hack to allow us to feed known types back into the type inference engine.
fn to_typep(ty: &Type, range: Range) -> TypeP {
    let qualified_to_identifier = |name: &QualifiedName| IdentifierP {
        segments: name
            .source_file
            .module
            .segments
            .iter()
            .map(|segment| segment.0.clone())
            .chain(std::iter::once(name.source_file.file.0.clone()))
            .chain(std::iter::once(name.name.clone()))
            .map(|s| NameP { name: s, range })
            .collect(),
    };

    match ty {
        Type::Named { name, parameters } => TypeP::Named {
            identifier: qualified_to_identifier(name),
            params: parameters.iter().map(|ty| to_typep(ty, range)).collect(),
        },
        Type::Variable {
            variable,
            parameters,
        } => TypeP::Named {
            identifier: IdentifierP {
                segments: vec![NameP {
                    name: variable.clone(),
                    range,
                }],
            },
            params: parameters.iter().map(|ty| to_typep(ty, range)).collect(),
        },
        Type::Function(l, r) => TypeP::Function(
            Box::new(to_typep(&*l, range)),
            Box::new(to_typep(&*r, range)),
        ),
        Type::Primitive(prim) => TypeP::Named {
            identifier: IdentifierP {
                segments: vec![NameP {
                    name: prim.to_string(),
                    range,
                }],
            },
            params: Vec::new(),
        },
        Type::Borrow { .. } => todo!(),
        Type::Impl { .. } => todo!(),
    }
}
