use std::{collections::BTreeSet, fmt::Display};

use quill_common::name::QualifiedName;
use quill_mir::{
    mir::{DefinitionBodyM, KnownValue, StatementKind},
    ProjectMIR,
};
use quill_type::Type;
use quill_type_deduce::replace_type_variables;

/// The monomorphisation of a project is a list of all the types, functions, and aspects that
/// were used throughout the project, with type parameters filled in to their actual values.
#[derive(Debug)]
pub struct Monomorphisation {
    pub types: BTreeSet<MonomorphisedType>,
    pub functions: BTreeSet<MonomorphisedFunction>,
    /// Tracks which monomorphisations of aspects have been used.
    /// This does *not* track which impls have been used.
    pub aspects: BTreeSet<MonomorphisedAspect>,
}

impl Monomorphisation {
    /// Monomorphise the project. We start by considering the "main" function, and then
    /// track everything that it calls, so that we can work out which concrete type parameters
    /// are used.
    pub fn new(mir: &ProjectMIR) -> Self {
        let mut mono = Self {
            types: BTreeSet::new(),
            functions: BTreeSet::new(),
            aspects: BTreeSet::new(),
        };

        mono.track_def(
            mir,
            mir.entry_point.clone(),
            MonomorphisationParameters::new(Vec::new()),
        );

        // println!("Mono: {:#?}", mono);

        mono
    }

    /// Assuming that this definition has the given possible monomorphisation parameters, track further required
    /// monomorphisation.
    fn track_def(
        &mut self,
        mir: &ProjectMIR,
        func: QualifiedName,
        mono: MonomorphisationParameters,
    ) {
        let def = &mir.files[&func.source_file].definitions[&func.name];
        if self.functions.insert(MonomorphisedFunction {
            func: func.clone(),
            mono: mono.clone(),
        }) {
            // Work out what functions are called (and what types are referenced) by this function.
            for info in def.local_variable_names.values() {
                let ty = replace_type_variables(
                    info.ty.clone(),
                    &def.type_variables,
                    &mono.type_parameters,
                );
                self.track_type(ty);
            }

            if let DefinitionBodyM::PatternMatch(cfg) = &def.body {
                for block in cfg.basic_blocks.values() {
                    for stmt in &block.statements {
                        if let StatementKind::InstanceSymbol {
                            name,
                            type_variables,
                            ..
                        } = &stmt.kind
                        {
                            self.track_def(
                                mir,
                                name.clone(),
                                MonomorphisationParameters::new(
                                    type_variables
                                        .iter()
                                        .cloned()
                                        .map(|ty| {
                                            replace_type_variables(
                                                ty,
                                                &def.type_variables,
                                                &mono.type_parameters,
                                            )
                                        })
                                        .collect(),
                                ),
                            );
                        }
                    }
                }
            }
        }
    }

    fn track_type(&mut self, ty: Type) {
        match ty {
            Type::Named { name, parameters } => {
                self.types.insert(MonomorphisedType {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                });
            }
            Type::Impl { name, parameters } => {
                self.aspects.insert(MonomorphisedAspect {
                    name,
                    mono: MonomorphisationParameters::new(parameters),
                });
            }
            _ => {}
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MonomorphisationParameters {
    type_parameters: Vec<Type>,
    special_case_arguments: Vec<KnownValue>,
}

impl Display for MonomorphisationParameters {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, ty) in self.type_parameters.iter().enumerate() {
            if i == 0 {
                write!(f, "{}", ty)?;
            } else {
                write!(f, ", {}", ty)?;
            }
        }
        write!(f, "]")?;
        write!(f, "(")?;
        for (i, val) in self.special_case_arguments.iter().enumerate() {
            let val_str = val.display_in_mono();
            if i == 0 {
                write!(f, "{}", val_str)?;
            } else {
                write!(f, ", {}", val_str)?;
            }
        }
        write!(f, ")")
    }
}

impl MonomorphisationParameters {
    pub fn new(type_parameters: Vec<Type>) -> Self {
        Self {
            type_parameters: type_parameters
                .into_iter()
                .map(Type::anonymise_borrows)
                .collect(),
            special_case_arguments: Vec::new(),
        }
    }

    /// Add a special-case argument.
    pub fn with_arg(mut self, arg: KnownValue) -> Self {
        self.special_case_arguments.push(arg);
        self
    }

    /// Add special-case arguments.
    pub fn with_args(mut self, args: impl IntoIterator<Item = KnownValue>) -> Self {
        self.special_case_arguments.extend(args);
        self
    }

    /// Get a reference to the type parameters.
    pub fn type_parameters(&self) -> &[Type] {
        self.type_parameters.as_slice()
    }

    /// Get a reference to the monomorphisation parameters's special case arguments.
    pub fn special_case_arguments(&self) -> &[KnownValue] {
        self.special_case_arguments.as_slice()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MonomorphisedType {
    pub name: QualifiedName,
    pub mono: MonomorphisationParameters,
}

impl Display for MonomorphisedType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t/{}", self.name)?;
        if !self.mono.type_parameters.is_empty() {
            write!(f, "[")?;
            for ty_param in &self.mono.type_parameters {
                write!(f, "{},", ty_param)?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MonomorphisedFunction {
    pub func: QualifiedName,
    pub mono: MonomorphisationParameters,
}

/// A monomorphisation of a function, but specialised to a specific amount of supplied arguments, and directness.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MonomorphisedCurriedFunction {
    pub func: MonomorphisedFunction,
    pub curry: CurryStatus,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CurryStatus {
    /// Must never contain a zero.
    pub curry_steps: Vec<u64>,
    /// If this is true, the function will be monomorphised as a "direct" function; no function pointer is supplied and
    /// all arguments before (but NOT including) the given curry steps are given as function parameters. The return type is a function object
    /// that will compute the result of the function when executed with an "indirect" function call (or multiple in a chain).
    /// If this is false, the function is considered "indirect"; a function pointer (representing this function) is supplied as
    /// the first parameter. The next n parameters are the params for the first curry step.
    ///
    /// For example, if `curry_steps = [1,1]`, `arity = 2`, and `direct = false` then the function's signature will be
    /// `(fobj0, first parameter) -> fobj1` where `fobj0` is a function object containing no data, and `fobj1` is a function
    /// object storing the first parameter, pointing to an this function with `curry_steps = [1]` and `direct = false`.
    ///
    /// If `curry_steps = [1,1]`, `arity = 2`, and `direct = true` then the function's signature will be
    /// `() -> fobj0` where `fobj0` if a function object containing no data and pointing to this function with `curry_steps = [1,1]`
    /// and `direct = false`.
    ///
    /// We can think of indirect functions as "going one level down the currying chain", since they always consume and emit a function
    /// object (unless, of course, this is the last currying step - in which case the actual function is executed and its return type
    /// becomes the only return value). Direct functions allow us to "jump inside the currying chain" - providing an amount of parameters,
    /// we can create a function object holding these parameters.
    pub direct: bool,
}

impl Display for CurryStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.curry_steps)?;
        if self.direct {
            write!(f, "d")
        } else {
            write!(f, "i")
        }
    }
}

impl Display for MonomorphisedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.func, self.mono)
    }
}

impl Display for MonomorphisedCurriedFunction {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.func, self.curry)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MonomorphisedAspect {
    pub name: QualifiedName,
    pub mono: MonomorphisationParameters,
}

impl Display for MonomorphisedAspect {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "a/{}", self.name)?;
        if !self.mono.type_parameters.is_empty() {
            write!(f, "[")?;
            for ty_param in &self.mono.type_parameters {
                write!(f, "{},", ty_param)?;
            }
            write!(f, "]")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionObjectDescriptor {
    pub func: MonomorphisedFunction,
    /// If this monomorphisation of this function requires a currying step,
    /// this contains the amount of parameters applied in the *last* such step.
    pub last_curry_step: Option<u64>,
}

impl Display for FunctionObjectDescriptor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "o/{}", self.func)?;
        if let Some(last) = self.last_curry_step {
            write!(f, "/{}", last)?;
        }
        Ok(())
    }
}

impl MonomorphisedCurriedFunction {
    pub fn function_object_descriptor(&self) -> FunctionObjectDescriptor {
        FunctionObjectDescriptor {
            func: self.func.clone(),
            last_curry_step: self.curry.curry_steps.last().copied(),
        }
    }
}
