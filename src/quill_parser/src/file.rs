use crate::{
    data_types::{DataP, EnumP},
    definition::DefinitionP,
    identifier::IdentifierP,
};

/// A single `.ql` file may export data types and definitions.
/// This `File` struct contains the parsed abstract syntax tree of a file.
#[derive(Debug)]
pub struct FileP {
    pub uses: Vec<UseP>,
    pub data: Vec<DataP>,
    pub enums: Vec<EnumP>,
    pub definitions: Vec<DefinitionP>,
}

#[derive(Debug)]
pub struct UseP {
    pub source_file: IdentifierP,
}
