use std::{collections::HashMap, fmt::Display};

use self::definition::Definition;

pub mod definition;
pub mod expr;
pub mod pattern;

/// A parsed and fully type checked source file.
/// No effort has been made to ensure semantic consistency or correctness,
/// just syntactic and type correctness.
#[derive(Debug)]
pub struct SourceFileHIR {
    pub definitions: HashMap<String, Definition>,
}

impl Display for SourceFileHIR {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Definitions:")?;
        for (def_name, def) in &self.definitions {
            writeln!(
                f,
                "---\n{} : ({}) -> {}",
                def_name,
                def.arg_types
                    .iter()
                    .map(|ty| ty.to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                def.return_type
            )?;
            writeln!(f, "{:#?}", def.body)?;
        }
        Ok(())
    }
}
