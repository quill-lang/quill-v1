//! Computes an index of all top-level items in a module,
//! storing type information. The module index is sufficient to determine the type
//! of any expression.

use std::{
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    fmt::Display,
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpMessage, HelpType, Severity},
    location::{
        ModuleIdentifier, Range, SourceFileIdentifier, SourceFileIdentifierSegment, SourceFileType,
    },
    name::QualifiedName,
};
use quill_parser::{file::FileP, identifier::NameP};
use quill_type::Type;

use crate::type_index::{ProjectTypesAspectsC, TypeDeclarationOrAspectC};

/// An index of all top-level items in a file.
///
/// Realistically this type should probably have the `I` suffix, but in my opinion it's pretty self-evident.
#[derive(Debug)]
pub struct FileIndex {
    pub types: BTreeMap<String, TypeDeclarationI>,
    pub definitions: BTreeMap<String, DefinitionI>,
    /// Maps enum variant names (True, Left) to the enum that contains them (Bool, Either)
    pub enum_variant_types: BTreeMap<String, String>,
    pub aspects: BTreeMap<String, AspectI>,
}

#[derive(Debug)]
pub struct ProjectIndex {
    files: BTreeMap<SourceFileIdentifier, FileIndex>,
    default_impls: DefaultImpls,
}

/// Tracks the definitions in a project which are marked as "default".
#[derive(Debug)]
pub struct DefaultImpls {
    /// Maps names of impls to a set of definition names.
    /// Each definition listed here has the type impl -> impl -> ... -> T
    /// where T is the name of the impl that is the key in this map.
    impls: BTreeMap<QualifiedName, BTreeSet<QualifiedName>>,
}

impl ProjectIndex {
    pub(crate) fn new(files: BTreeMap<SourceFileIdentifier, FileIndex>) -> DiagnosticResult<Self> {
        collate_default_impls(&files).map(|default_impls| Self {
            files,
            default_impls,
        })
    }

    pub fn is_file_indexed(&self, file: &SourceFileIdentifier) -> bool {
        self.files.contains_key(file)
    }

    pub fn get_file_index(&self, file: &SourceFileIdentifier) -> &FileIndex {
        &self.files[file]
    }

    pub fn type_decl(&self, name: &QualifiedName) -> &TypeDeclarationI {
        &self.files[&name.source_file].types[&name.name]
    }

    pub fn definition(&self, name: &QualifiedName) -> &DefinitionI {
        &self.files[&name.source_file].definitions[&name.name]
    }

    pub fn aspect(&self, name: &QualifiedName) -> &AspectI {
        &self.files[&name.source_file].aspects[&name.name]
    }

    pub fn default_impls(&self, name: &QualifiedName) -> &BTreeSet<QualifiedName> {
        &self.default_impls.impls[name]
    }
}

/// Searches each file for definitions marked with "default" and
/// collates them into this list.
/// Any definitions which are not of the type impl -> impl -> ... -> T
/// will be discarded, and an error message raised.
fn collate_default_impls(
    files: &BTreeMap<SourceFileIdentifier, FileIndex>,
) -> DiagnosticResult<DefaultImpls> {
    let mut messages = Vec::new();
    let mut impls = BTreeMap::<QualifiedName, BTreeSet<QualifiedName>>::new();
    for (source_file, index) in files {
        for (def_name, def) in &index.definitions {
            if let Some(range) = def.default {
                // First, check if this is a valid "default" definition.
                let mut result_type = def.symbol_type.clone();
                loop {
                    match result_type {
                        Type::Function(l, r) => {
                            // Check if the left-hand type was an impl.
                            if !matches!(&*l, Type::Impl { .. }) {
                                messages.push(ErrorMessage::new(
                                    format!(
                                        "arguments to a `default` function can only be impls, but there was an argument of type {}",
                                        l,
                                    ),
                                    Severity::Error,
                                    Diagnostic::at(source_file, &range),

                                ));
                                break;
                            }
                            result_type = *r;
                        }
                        Type::Impl { name, .. } => {
                            // This was a valid "default" definition.
                            impls.entry(name).or_default().insert(QualifiedName {
                                source_file: source_file.clone(),
                                name: def_name.clone(),
                                range,
                            });
                            break;
                        }
                        other => {
                            messages.push(ErrorMessage::new(
                                format!(
                                    "type of `default` function can only be an impl, but found type {}",
                                    other,
                                ),
                                Severity::Error,
                                Diagnostic::at(source_file, &range),
                            ));
                            break;
                        }
                    }
                }
            }
        }
    }
    DiagnosticResult::ok_with_many(DefaultImpls { impls }, messages)
}

/// A type declaration, e.g. `data Bool = True | False`.
#[derive(Debug)]
pub struct TypeDeclarationI {
    /// This is kept here mostly because it contains the `Range` where it was defined.
    pub name: NameP,
    pub decl_type: TypeDeclarationTypeI,
}

/// Either a data declaration, a new type wrapper, a type alias, or a dependent type.
#[derive(Debug)]
pub enum TypeDeclarationTypeI {
    Data(DataI),
    Enum(EnumI),
}

/// A `data` declaration.
#[derive(Debug)]
pub struct DataI {
    /// Where was this data declaration written?
    pub range: Range,
    pub type_params: Vec<TypeParameter>,
    pub type_ctor: TypeConstructorI,
}

/// A `enum` declaration.
#[derive(Debug)]
pub struct EnumI {
    /// Where was this enum declaration written?
    pub range: Range,
    pub type_params: Vec<TypeParameter>,
    pub variants: Vec<EnumVariant>,
}

#[derive(Debug)]
pub struct EnumVariant {
    pub name: NameP,
    pub type_ctor: TypeConstructorI,
}

#[derive(Debug)]
pub struct TypeConstructorI {
    pub fields: Vec<(NameP, Type)>,
}

/// A top-level definition, i.e. a `def` block.
/// TODO: In the future, we will need to add a list of constraints to definitions and data blocks.
#[derive(Debug)]
pub struct DefinitionI {
    /// If this definition was marked "default", the range of this token is given here.
    pub default: Option<Range>,
    pub name: NameP,
    pub type_variables: Vec<TypeParameter>,
    pub symbol_type: Type,
}

#[derive(Debug, Clone)]
pub struct TypeParameter {
    pub name: String,
    /// A type variable may have one or more unnamed parameters, e.g. `F[_]` is a common type for a functor.
    /// This field stores how many such parameters the type variable has.
    pub parameters: u32,
}

impl Display for TypeParameter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)?;
        if self.parameters > 0 {
            write!(f, "[{}]", self.parameters)?;
        }
        Ok(())
    }
}

/// An aspect.
#[derive(Debug)]
pub struct AspectI {
    pub name: NameP,
    pub type_variables: Vec<TypeParameter>,
    pub definitions: Vec<DefinitionI>,
}

/// Returns a generic error message about multiply defined symbols, making sure that the "earlier" symbol
/// actually was the one that appeared earlier in the file.
fn name_used_earlier(
    source_file: &SourceFileIdentifier,
    range1: Range,
    range2: Range,
) -> ErrorMessage {
    ErrorMessage::new_with(
        String::from("this name was used earlier for another definition"),
        Severity::Error,
        Diagnostic::at(source_file, &range1.max(range2)),
        HelpMessage {
            message: String::from("previously used here"),
            help_type: HelpType::Note,
            diagnostic: Diagnostic::at(source_file, &range1.min(range2)),
        },
    )
}

/// Represents a type declaration that may be in a different source file.
pub(crate) struct ForeignItemDeclarationC<'a> {
    pub source_file: SourceFileIdentifier,
    pub decl: &'a TypeDeclarationOrAspectC,
}

pub struct UsedFile {
    pub file: SourceFileIdentifier,
}

/// Produces a list of all the files (including itself) that are used in this file.
/// `project_files` is a predicate saying whether the given file is in the project.
pub fn compute_used_files(
    source_file: &SourceFileIdentifier,
    file_parsed: &FileP,
    project_files: impl Fn(&SourceFileIdentifier) -> bool,
) -> DiagnosticResult<Vec<UsedFile>> {
    let mut result = vec![UsedFile {
        file: source_file.clone(),
    }];
    let mut messages = Vec::new();
    for used_file in &file_parsed.uses {
        // Resolve the used file into a concrete source file identifier.
        // If we're in foo::bar and we're looking for baz::qux, we search
        // - foo::bar::baz::qux
        // - foo::baz::qux
        // - baz::qux
        let mut module = source_file.module.clone();
        let mut used_file_segments = used_file.source_file.segments.clone();
        let used_file_file: SourceFileIdentifierSegment =
            used_file_segments.pop().unwrap().name.clone().into();
        let used_file_module = used_file_segments
            .into_iter()
            .map(|name| name.name.into())
            .collect::<Vec<_>>();
        loop {
            let used_file_id = SourceFileIdentifier {
                module: ModuleIdentifier {
                    segments: module
                        .segments
                        .iter()
                        .cloned()
                        .chain(used_file_module.clone())
                        .collect(),
                },
                file: used_file_file.clone(),
                file_type: SourceFileType::Quill,
            };
            if project_files(&used_file_id) {
                result.push(UsedFile { file: used_file_id });
                break;
            }

            module.segments.pop();
            if module.segments.is_empty() {
                // We couldn't find the package.
                messages.push(ErrorMessage::new(
                    "could not find this package".to_string(),
                    Severity::Error,
                    Diagnostic::at(source_file, &used_file.source_file),
                ));
                break;
            }
        }
    }
    DiagnosticResult::ok_with_many(result, messages)
}

/// Work out what type names and aspect names are visible inside a file.
fn compute_visible_types_and_aspects<'a>(
    source_file: &'a SourceFileIdentifier,
    file_parsed: &'a FileP,
    project_types: &'a ProjectTypesAspectsC,
) -> DiagnosticResult<BTreeMap<&'a str, ForeignItemDeclarationC<'a>>> {
    let mut visible_types = BTreeMap::<&str, Vec<ForeignItemDeclarationC>>::new();
    let mut messages = Vec::new();

    let (used_files, more_messages) = compute_used_files(source_file, file_parsed, |name| {
        project_types.contains_key(name)
    })
    .destructure();
    messages.extend(more_messages);
    for file in used_files.unwrap() {
        for (ty, decl) in &project_types[&file.file] {
            visible_types
                .entry(ty.as_str())
                .or_default()
                .push(ForeignItemDeclarationC {
                    source_file: file.file.clone(),
                    decl,
                });
        }
    }

    // Now generate error messages if the multimap contains any duplicate entries.
    let result = visible_types.into_iter().filter_map(|(ty, mut decls)| {
        if decls.len() == 1 {
            Some((ty, decls.pop().unwrap()))
        } else {
            messages.push(ErrorMessage::new_with_many(
                format!("a type with name `{}` was imported from multiple locations, which could cause ambiguity, so this name will not be usable in this file", ty),
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

    DiagnosticResult::ok_with_many(result, messages)
}

/// Computes the index for a file.
pub(crate) fn index(
    source_file: &SourceFileIdentifier,
    file_parsed: &FileP,
    project_types: &ProjectTypesAspectsC,
) -> DiagnosticResult<FileIndex> {
    let mut messages = Vec::new();
    let visible_types = {
        let (visible_types, more_messages) =
            compute_visible_types_and_aspects(source_file, file_parsed, project_types)
                .destructure();
        messages.extend(more_messages);
        visible_types.unwrap()
    };

    let mut types = BTreeMap::<String, TypeDeclarationI>::new();
    let mut definitions = BTreeMap::<String, DefinitionI>::new();
    let mut enum_variant_types = BTreeMap::<String, String>::new();
    let mut aspects = BTreeMap::<String, AspectI>::new();

    for definition in &file_parsed.definitions {
        match definitions.entry(definition.decl.name.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    definition.decl.name.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add this definition into the map.
                let symbol_type = crate::type_resolve::resolve_typep(
                    source_file,
                    &definition.decl.definition_type,
                    &definition
                        .decl
                        .type_parameters
                        .iter()
                        .map(|id| id.name.name.clone())
                        .collect(),
                    &visible_types,
                );
                let (symbol_type, mut inner_messages) = symbol_type.destructure();
                messages.append(&mut inner_messages);
                if let Some(symbol_type) = symbol_type {
                    let definition = DefinitionI {
                        default: definition.decl.default,
                        name: definition.decl.name.clone(),
                        type_variables: definition
                            .decl
                            .type_parameters
                            .iter()
                            .map(|param| TypeParameter {
                                name: param.name.name.clone(),
                                parameters: param.parameters,
                            })
                            .collect(),
                        symbol_type,
                    };
                    vacant.insert(definition);
                }
            }
        }
    }

    for data in &file_parsed.data {
        match types.entry(data.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    data.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add the definition into the map.
                let type_params = data
                    .type_params
                    .iter()
                    .map(|ident| ident.name.name.clone())
                    .collect::<BTreeSet<_>>();

                let type_ctor = data
                    .type_ctor
                    .fields
                    .iter()
                    .map(|field| {
                        let ty = crate::type_resolve::resolve_typep(
                            source_file,
                            &field.ty,
                            &type_params,
                            &visible_types,
                        );
                        ty.map(|ty| (field.name.clone(), ty))
                    })
                    .collect::<DiagnosticResult<Vec<_>>>()
                    .map(|fields| TypeConstructorI { fields });
                let (_, mut inner_messages) = type_ctor
                    .map(|type_ctor| {
                        let datai = DataI {
                            range: data.identifier.range,
                            type_params: data
                                .type_params
                                .iter()
                                .map(|param| TypeParameter {
                                    name: param.name.name.clone(),
                                    parameters: param.parameters,
                                })
                                .collect(),
                            type_ctor,
                        };
                        vacant.insert(TypeDeclarationI {
                            name: data.identifier.clone(),
                            decl_type: TypeDeclarationTypeI::Data(datai),
                        });
                    })
                    .destructure();
                messages.append(&mut inner_messages);
            }
        }
    }

    for an_enum in &file_parsed.enums {
        match types.entry(an_enum.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    an_enum.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add the definition into the map.
                let type_params = an_enum
                    .type_params
                    .iter()
                    .map(|ident| ident.name.name.clone())
                    .collect::<BTreeSet<_>>();

                let variants = an_enum
                    .alternatives
                    .iter()
                    .map(|variant| {
                        variant
                            .type_ctor
                            .fields
                            .iter()
                            .map(|field| {
                                let ty = crate::type_resolve::resolve_typep(
                                    source_file,
                                    &field.ty,
                                    &type_params,
                                    &visible_types,
                                );
                                ty.map(|ty| (field.name.clone(), ty))
                            })
                            .collect::<DiagnosticResult<Vec<_>>>()
                            .map(|fields| EnumVariant {
                                name: variant.name.clone(),
                                type_ctor: TypeConstructorI { fields },
                            })
                    })
                    .collect::<DiagnosticResult<Vec<_>>>();

                let (_, mut inner_messages) = variants
                    .bind(|variants| {
                        let mut messages = Vec::new();

                        for variant in &variants {
                            match enum_variant_types.entry(variant.name.name.clone()) {
                                Entry::Occupied(occupied) => messages.push(ErrorMessage::new(
                                    format!(
                                        "an enum variant called `{}` was already defined inside `{}`",
                                        variant.name.name,
                                        occupied.get(),
                                    ),
                                    Severity::Error,
                                    Diagnostic::at(source_file, &variant.name.range),
                                )),
                                Entry::Vacant(vacant) => {
                                    vacant.insert(an_enum.identifier.name.clone());
                                }
                            }
                        }

                        let enumi = EnumI {
                            range: an_enum.identifier.range,
                            type_params: an_enum
                                .type_params
                                .iter()
                                .map(|param| TypeParameter {
                                    name: param.name.name.clone(),
                                    parameters: param.parameters,
                                })
                                .collect(),
                            variants,
                        };

                        vacant.insert(TypeDeclarationI {
                            name: an_enum.identifier.clone(),
                            decl_type: TypeDeclarationTypeI::Enum(enumi),
                        });

                        DiagnosticResult::ok_with_many((), messages)
                    })
                    .destructure();

                messages.append(&mut inner_messages);
            }
        }
    }

    for aspect in &file_parsed.aspects {
        match aspects.entry(aspect.identifier.name.clone()) {
            Entry::Occupied(occupied) => {
                messages.push(name_used_earlier(
                    source_file,
                    aspect.identifier.range,
                    occupied.get().name.range,
                ));
            }
            Entry::Vacant(vacant) => {
                // Let's add this aspect into the map.
                let definitions = aspect
                    .definitions
                    .iter()
                    .map(|def| {
                        crate::type_resolve::resolve_typep(
                            source_file,
                            &def.definition_type,
                            &aspect
                                .type_params
                                .iter()
                                .chain(def.type_parameters.iter())
                                .map(|id| id.name.name.clone())
                                .collect(),
                            &visible_types,
                        )
                        .map(|symbol_type| DefinitionI {
                            default: None,
                            name: def.name.clone(),
                            type_variables: def
                                .type_parameters
                                .iter()
                                .map(|param| TypeParameter {
                                    name: param.name.name.clone(),
                                    parameters: param.parameters,
                                })
                                .collect(),
                            symbol_type,
                        })
                    })
                    .collect::<DiagnosticResult<Vec<_>>>();
                let (definitions, mut inner_messages) = definitions.destructure();
                messages.append(&mut inner_messages);
                if let Some(definitions) = definitions {
                    let aspect = AspectI {
                        name: aspect.identifier.clone(),
                        type_variables: aspect
                            .type_params
                            .iter()
                            .map(|param| TypeParameter {
                                name: param.name.name.clone(),
                                parameters: param.parameters,
                            })
                            .collect(),
                        definitions,
                    };
                    vacant.insert(aspect);
                }
            }
        }
    }

    let index = FileIndex {
        types,
        definitions,
        enum_variant_types,
        aspects,
    };
    DiagnosticResult::ok_with_many(index, messages)
}
