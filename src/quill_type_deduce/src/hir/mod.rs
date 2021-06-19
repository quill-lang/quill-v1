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
                "  {} : {:?} -> {}",
                def_name, def.arg_types, def.return_type
            )?;
        }
        Ok(())
    }
}
