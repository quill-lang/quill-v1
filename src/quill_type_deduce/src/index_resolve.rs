use std::collections::HashMap;

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, Severity},
    location::{Range, Ranged, SourceFileIdentifier},
    name::QualifiedName,
};
use quill_index::{DefinitionI, ProjectIndex, TypeDeclarationTypeI, TypeParameter};
use quill_parser::IdentifierP;
use quill_type::Type;

use crate::{type_check::TypeVariable, type_resolve::TypeVariableId};

/// When a type constructor is used in code, e.g. `False`.
/// For type constructor declarations, see `TypeConstructor`.
#[derive(Debug, Clone)]
pub struct TypeConstructorInvocation {
    /// The data type that the type constructor will create.
    pub data_type: QualifiedName,
    /// How many type parameters does this data type have?
    pub num_parameters: u32,
    /// The range where the type ctor was used in code.
    pub range: Range,
}

/// Replaces named type parameters e.g. `T` with their concrete types.
/// For example, calling this function on `Just[T]`, when `named_type_parameters = [T]` and `concrete_type_parameters = [Bool]` gives `Just[Bool]`.
pub fn replace_type_variables(
    ty: Type,
    named_type_parameters: &[TypeParameter],
    concrete_type_parameters: &[Type],
) -> Type {
    match ty {
        Type::Named { name, parameters } => Type::Named {
            name,
            parameters: parameters
                .into_iter()
                .map(|param| {
                    replace_type_variables(param, named_type_parameters, concrete_type_parameters)
                })
                .collect(),
        },
        Type::Function(l, r) => Type::Function(
            Box::new(replace_type_variables(
                *l,
                named_type_parameters,
                concrete_type_parameters,
            )),
            Box::new(replace_type_variables(
                *r,
                named_type_parameters,
                concrete_type_parameters,
            )),
        ),
        Type::Variable {
            variable,
            parameters,
        } => {
            // Is this type variable in our list of named type variables?
            if let Some((i, _)) = named_type_parameters
                .iter()
                .enumerate()
                .find(|(_, param)| param.name == variable)
            {
                // We need to replace the parameters, if this variable is for a higher kinded type.
                // For instance, if this variable has type `F[Bool]` and we know that `F = Vec`, then we get `Vec[Bool]`.
                let replacement = concrete_type_parameters[i].clone();
                match replacement {
                    Type::Named {
                        name,
                        parameters: replacement_parameters,
                    } => {
                        if replacement_parameters.is_empty() {
                            Type::Named {
                                name,
                                parameters: parameters
                                    .into_iter()
                                    .map(|param| {
                                        replace_type_variables(
                                            param,
                                            named_type_parameters,
                                            concrete_type_parameters,
                                        )
                                    })
                                    .collect(),
                            }
                        } else {
                            panic!("can't apply type parameters to an already-quantified type")
                        }
                    }
                    Type::Variable {
                        variable,
                        parameters: replacement_parameters,
                    } => {
                        if replacement_parameters.is_empty() {
                            Type::Variable {
                                variable,
                                parameters: parameters
                                    .into_iter()
                                    .map(|param| {
                                        replace_type_variables(
                                            param,
                                            named_type_parameters,
                                            concrete_type_parameters,
                                        )
                                    })
                                    .collect(),
                            }
                        } else {
                            panic!("can't apply type parameters to an already-quantified type")
                        }
                    }
                    Type::Function(_, _) => {
                        panic!("can't apply type parameters to functions")
                    }
                    Type::Primitive(_) => {
                        panic!("can't apply type parameters to primitive types")
                    }
                }
            } else {
                // This was not in the list; just return it verbatim.
                Type::Variable {
                    variable,
                    parameters,
                }
            }
        }
        Type::Primitive(prim) => Type::Primitive(prim),
    }
}

pub struct InstantiationResult {
    pub result: TypeVariable,
    pub ids: HashMap<String, TypeVariable>,
    pub higher_kinded_ids: HashMap<String, HashMap<Vec<Type>, TypeVariable>>,
}

/// You can instantiate a type into a type variable,
/// by letting all unknown variables be polymorphic type variables, over which the type is quantified.
/// This function returns the type variable, along with the map of quantifier names to type variable IDs,
/// and the map of higher-kinded quantifier names to the map converting lists of parameters to their assigned IDs.
pub fn instantiate(ty: &Type) -> InstantiationResult {
    let mut ids = HashMap::new();
    let mut higher_kinded_ids = HashMap::new();
    let result = instantiate_with(ty, &mut ids, &mut higher_kinded_ids);
    InstantiationResult {
        result,
        ids,
        higher_kinded_ids,
    }
}

/// While we're instantiating a type, we need to keep track of all of the named type variables
/// and which type variables we've assigned them.
/// The map of higher kinded IDs maps variable names to lists of parameters to type variables.
pub fn instantiate_with(
    ty: &Type,
    ids: &mut HashMap<String, TypeVariable>,
    higher_kinded_ids: &mut HashMap<String, HashMap<Vec<Type>, TypeVariable>>,
) -> TypeVariable {
    match ty {
        Type::Named { name, parameters } => TypeVariable::Named {
            name: name.clone(),
            parameters: parameters
                .iter()
                .map(|p| instantiate_with(p, ids, higher_kinded_ids))
                .collect::<Vec<_>>(),
        },
        Type::Function(l, r) => {
            let l2 = instantiate_with(l, ids, higher_kinded_ids);
            let r2 = instantiate_with(r, ids, higher_kinded_ids);
            TypeVariable::Function(Box::new(l2), Box::new(r2))
        }
        Type::Variable {
            variable,
            parameters,
        } => {
            if parameters.is_empty() {
                ids.entry(variable.clone())
                    .or_insert_with(|| TypeVariable::Unknown {
                        id: TypeVariableId::default(),
                    })
                    .clone()
            } else {
                // Higher kinded types get one type variable for each instantiation.
                // For instance, `F[T]` and `F[K]` are given *different* type variables.
                // The precise distribution of type variables is specified in the third parameter to this function.
                higher_kinded_ids
                    .entry(variable.clone())
                    .or_default()
                    .entry(parameters.clone())
                    .or_insert_with(|| TypeVariable::Unknown {
                        id: TypeVariableId::default(),
                    })
                    .clone()
            }
        }
        Type::Primitive(prim) => TypeVariable::Primitive(*prim),
    }
}

/// You can convert a type into a type variable without quantifying over any variable types.
/// This is used primarily for arguments and return types of functions, in which we should never
/// quantify over the type variables.
pub fn as_variable(ty: &Type) -> TypeVariable {
    match ty {
        Type::Named { name, parameters } => TypeVariable::Named {
            name: name.clone(),
            parameters: parameters
                .iter()
                .map(|p| as_variable(p))
                .collect::<Vec<_>>(),
        },
        Type::Function(l, r) => {
            let l2 = as_variable(l);
            let r2 = as_variable(r);
            TypeVariable::Function(Box::new(l2), Box::new(r2))
        }
        Type::Variable {
            variable,
            parameters,
        } => TypeVariable::Variable {
            variable: variable.clone(),
            parameters: parameters
                .iter()
                .map(|p| as_variable(p))
                .collect::<Vec<_>>(),
        },
        Type::Primitive(prim) => TypeVariable::Primitive(*prim),
    }
}

/// Resolves the use of a type constructor.
pub fn resolve_type_constructor(
    source_file: &SourceFileIdentifier,
    identifier: &IdentifierP,
    project_index: &ProjectIndex,
) -> DiagnosticResult<TypeConstructorInvocation> {
    // We don't have `import`-style statements yet, so let's just only search for types in the current module path.
    let file_index = &project_index[source_file];
    // A type constructor identifier is the name of the type.
    if identifier.segments.len() == 1 {
        match file_index.types.get(&identifier.segments[0].name) {
            Some(data_name) => {
                if let TypeDeclarationTypeI::Data(datai) = &data_name.decl_type {
                    let data_type = QualifiedName {
                        source_file: source_file.clone(),
                        name: data_name.name.name.clone(),
                        range: datai.range,
                    };
                    DiagnosticResult::ok(TypeConstructorInvocation {
                        data_type,
                        range: identifier.range(),
                        num_parameters: datai.type_params.len() as u32,
                    })
                } else {
                    unreachable!()
                }
            }
            None => DiagnosticResult::fail(ErrorMessage::new(
                String::from("could not resolve type constructor"),
                Severity::Error,
                Diagnostic::at(source_file, &identifier.range()),
            )),
        }
    } else {
        DiagnosticResult::fail(ErrorMessage::new(
            "too many segments in qualified name".to_string(),
            Severity::Error,
            Diagnostic::at(source_file, identifier),
        ))
    }
}

/// Resolves a definition. Returns the source file that it was defined in, along with the definition itself.
pub fn resolve_definition<'a>(
    source_file: &SourceFileIdentifier,
    identifier: &IdentifierP,
    project_index: &'a ProjectIndex,
) -> DiagnosticResult<(&'a SourceFileIdentifier, &'a DefinitionI)> {
    // We don't have `import`-style statements yet, so let's just only search for types in the current module path.
    if let Some((source_file_long_lifetime, module_index)) =
        project_index.get_key_value(source_file)
    {
        if identifier.segments.len() == 1 {
            match module_index.definitions.get(&identifier.segments[0].name) {
                Some(symbol) => DiagnosticResult::ok((source_file_long_lifetime, symbol)),
                None => DiagnosticResult::fail(ErrorMessage::new(
                    String::from("could not resolve definition"),
                    Severity::Error,
                    Diagnostic::at(source_file, &identifier.range()),
                )),
            }
        } else {
            DiagnosticResult::fail(ErrorMessage::new(
                String::from("identifier had too many segments"),
                Severity::Error,
                Diagnostic::at(source_file, &identifier.range()),
            ))
        }
    } else {
        panic!("module was not in index")
    }
}

#[cfg(test)]
mod tests {
    use quill_common::name::QualifiedName;
    use quill_index::TypeParameter;
    use quill_type::Type;

    use super::replace_type_variables;

    #[test]
    fn replace_type_variables_test() {
        // Replace A[T] with A[_]=Vec[_] and T=Bool to give Vec[Bool].
        let replacement = replace_type_variables(
            Type::Variable {
                variable: "A".to_string(),
                parameters: vec![Type::Variable {
                    variable: "T".to_string(),
                    parameters: Vec::new(),
                }],
            },
            &[
                TypeParameter {
                    name: "A".to_string(),
                    parameters: 1,
                },
                TypeParameter {
                    name: "T".to_string(),
                    parameters: 0,
                },
            ],
            &[
                Type::Named {
                    name: QualifiedName::test_name("Vec"),
                    // Empty list of params because we don't know what the parameters are yet - not even as named variables.
                    parameters: Vec::new(),
                },
                Type::Named {
                    name: QualifiedName::test_name("Bool"),
                    parameters: Vec::new(),
                },
            ],
        );
        let expected = Type::Named {
            name: QualifiedName::test_name("Vec"),
            parameters: vec![Type::Named {
                name: QualifiedName::test_name("Bool"),
                parameters: Vec::new(),
            }],
        };
        assert_eq!(replacement, expected);
    }

    #[test]
    fn replace_type_variables_test2() {
        // Replace A[T] with A[_]=F[_] and T=R to give F[R].
        let replacement = replace_type_variables(
            Type::Variable {
                variable: "A".to_string(),
                parameters: vec![Type::Variable {
                    variable: "T".to_string(),
                    parameters: Vec::new(),
                }],
            },
            &[
                TypeParameter {
                    name: "A".to_string(),
                    parameters: 1,
                },
                TypeParameter {
                    name: "T".to_string(),
                    parameters: 0,
                },
            ],
            &[
                Type::Variable {
                    variable: "F".to_string(),
                    // Empty list of params because we don't know what the parameters are yet - not even as named variables.
                    parameters: Vec::new(),
                },
                Type::Variable {
                    variable: "R".to_string(),
                    parameters: Vec::new(),
                },
            ],
        );
        let expected = Type::Variable {
            variable: "F".to_string(),
            parameters: vec![Type::Variable {
                variable: "R".to_string(),
                parameters: Vec::new(),
            }],
        };
        assert_eq!(replacement, expected);
    }
}
