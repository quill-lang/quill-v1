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
    /// The data type that the type constructor belongs to.
    pub data_type: QualifiedName,
    /// The name of the type constructor that was called.
    pub type_ctor: String,
    /// The range where the type ctor was used in code.
    pub range: Range,
}

/// Replaces named type parameters e.g. `a` with their concrete types.
/// For example, calling this function on `Just a`, when `named_type_parameters = [a]` and `concrete_type_parameters = [Bool]` gives `Just Bool`.
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
                            Type::Named { name, parameters }
                        } else {
                            panic!("can't apply type parameters to an already-quantified type")
                        }
                    }
                    Type::Variable { .. } => {
                        panic!("can't apply type parameters to variables")
                    }
                    Type::Function(_, _) => {
                        panic!("can't apply type parameters to functions")
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
    }
}

/// You can instantiate a type into a type variable,
/// by letting all unknown variables be polymorphic type variables, over which the type is quantified.
/// This function returns the type variable, along with the map of quantifier names to type variable IDs.
pub fn instantiate(ty: &Type) -> (TypeVariable, HashMap<String, TypeVariableId>) {
    let mut map = HashMap::new();
    let result = instantiate_with(ty, &mut map);
    (result, map)
}

/// While we're instantiating a type, we need to keep track of all of the named type variables
/// and which IDs we've assigned them.
fn instantiate_with(ty: &Type, ids: &mut HashMap<String, TypeVariableId>) -> TypeVariable {
    match ty {
        Type::Named { name, parameters } => TypeVariable::Named {
            name: name.clone(),
            parameters: parameters
                .iter()
                .map(|p| instantiate_with(p, ids))
                .collect::<Vec<_>>(),
        },
        Type::Function(l, r) => {
            let l2 = instantiate_with(l, ids);
            let r2 = instantiate_with(r, ids);
            TypeVariable::Function(Box::new(l2), Box::new(r2))
        }
        Type::Variable {
            variable,
            parameters,
        } => TypeVariable::Unknown {
            id: *ids
                .entry(variable.clone())
                .or_insert_with(TypeVariableId::default),
            parameters: parameters
                .iter()
                .map(|p| instantiate_with(p, ids))
                .collect(),
        },
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
    // A type constructor identifier is either:
    // a) the name of the type (means the default constructor), or
    // b) the name of the type then `::` then the constructor name
    // First, check for (a), then check (b).
    if identifier.segments.len() == 1 {
        match file_index.types.get(&identifier.segments[0].name) {
            Some(data_name) => {
                let TypeDeclarationTypeI::Data(datai) = &data_name.decl_type;
                let data_type = QualifiedName {
                    source_file: source_file.clone(),
                    name: data_name.name.name.clone(),
                    range: datai.range,
                };
                let ctor_name = data_name.name.name.clone();
                if datai
                    .type_ctors
                    .iter()
                    .find(|ctor| ctor.name == ctor_name)
                    .is_some()
                {
                    DiagnosticResult::ok(TypeConstructorInvocation {
                        data_type,
                        type_ctor: ctor_name,
                        range: identifier.range(),
                    })
                } else {
                    DiagnosticResult::fail(ErrorMessage::new(
                        format!(
                            "data type `{}` did not have a constructor called `{}`",
                            data_type, ctor_name
                        ),
                        Severity::Error,
                        Diagnostic::at(source_file, &identifier.range()),
                    ))
                }
            }
            None => DiagnosticResult::fail(ErrorMessage::new(
                String::from("could not resolve type constructor"),
                Severity::Error,
                Diagnostic::at(source_file, &identifier.range()),
            )),
        }
    } else {
        match file_index.types.get(&identifier.segments[0].name) {
            Some(data_name) => {
                let TypeDeclarationTypeI::Data(datai) = &data_name.decl_type;
                let data_type = QualifiedName {
                    source_file: source_file.clone(),
                    name: data_name.name.name.clone(),
                    range: datai.range,
                };
                let ctor_name = identifier.segments[1].name.clone();
                if datai
                    .type_ctors
                    .iter()
                    .find(|ctor| ctor.name == ctor_name)
                    .is_some()
                {
                    DiagnosticResult::ok(TypeConstructorInvocation {
                        data_type,
                        type_ctor: ctor_name,
                        range: identifier.range(),
                    })
                } else {
                    DiagnosticResult::fail(ErrorMessage::new(
                        format!(
                            "data type `{}` did not have a constructor called `{}`",
                            data_type, ctor_name
                        ),
                        Severity::Error,
                        Diagnostic::at(source_file, &identifier.range()),
                    ))
                }
            }
            None => DiagnosticResult::fail(ErrorMessage::new(
                String::from("could not resolve type constructor"),
                Severity::Error,
                Diagnostic::at(source_file, &identifier.range()),
            )),
        }
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
