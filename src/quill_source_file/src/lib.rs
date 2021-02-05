use std::{
    collections::HashMap,
    fmt::{Debug, Display},
    path::PathBuf,
    time::SystemTime,
};

use tokio::{fs::File, io::BufReader, sync::RwLock};

/// A fragment of the canonical name for a source file.
/// This does not include things like slashes to separate directories, double periods to denote going up a directory, or file extensions.
#[derive(Clone)]
pub struct SourceFileIdentifierSegment(pub String);

impl Debug for SourceFileIdentifierSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for SourceFileIdentifierSegment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl<S> From<S> for SourceFileIdentifierSegment
where
    S: Into<String>,
{
    fn from(s: S) -> Self {
        SourceFileIdentifierSegment(s.into())
    }
}

#[derive(Clone)]
pub struct ModuleIdentifier {
    segments: Vec<SourceFileIdentifierSegment>,
}

impl Debug for ModuleIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, fragment) in self.segments.iter().enumerate() {
            if i != 0 {
                write!(f, "::")?;
            }
            write!(f, "{}", fragment)?;
        }
        Ok(())
    }
}

impl Display for ModuleIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl From<Vec<String>> for ModuleIdentifier {
    fn from(segments: Vec<String>) -> Self {
        Self {
            segments: segments
                .into_iter()
                .map(SourceFileIdentifierSegment)
                .collect(),
        }
    }
}

impl From<ModuleIdentifier> for PathBuf {
    fn from(identifier: ModuleIdentifier) -> Self {
        identifier
            .segments
            .into_iter()
            .map(|fragment| fragment.0)
            .collect()
    }
}

#[derive(Clone)]
pub struct SourceFileIdentifier {
    pub module: ModuleIdentifier,
    pub file: SourceFileIdentifierSegment,
}

impl Debug for SourceFileIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.module.segments.is_empty() {
            write!(f, "{}", self.file)
        } else {
            write!(f, "{}::{}", self.module, self.file)
        }
    }
}

impl Display for SourceFileIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl From<SourceFileIdentifier> for PathBuf {
    fn from(identifier: SourceFileIdentifier) -> Self {
        PathBuf::from(identifier.module).join(identifier.file.0)
    }
}

/// If a source file's contents could not be loaded, why was this?
#[derive(Debug)]
pub enum SourceFileLoadError {
    IO(std::io::Error),
}

/// A single file of source code.
pub struct SourceFile {
    contents: String,
    modified_time: SystemTime,
}

impl Debug for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "source file modified at {:?}", self.modified_time)
    }
}

impl SourceFile {
    pub fn get_contents(&self) -> &str {
        self.contents.as_str()
    }

    pub fn last_modified(&self) -> SystemTime {
        self.modified_time
    }
}

/// A tree of source files and other modules.
#[derive(Debug, Default)]
pub struct Module {
    pub submodules: HashMap<String, Module>,
    pub source_files: HashMap<String, Result<SourceFile, SourceFileLoadError>>,
}

/// Represents the file structure of an entire package on disk.
/// A package is a folder that produces some kind of compiled output file,
/// which could be a binary, a static library, a shared object, a WASM module,
/// or something else of that kind.
pub struct PackageFileSystem {
    pub directory: PathBuf,
    root_module: RwLock<Module>,
}

impl PackageFileSystem {
    pub fn new(directory: PathBuf) -> Self {
        Self {
            directory,
            root_module: RwLock::new(Module::default()),
        }
    }

    async fn with_module<F, T>(&self, identifier: &ModuleIdentifier, func: F) -> T
    where
        F: FnOnce(&mut Module) -> T,
    {
        let mut guard = self.root_module.write().await;
        let mut module = &mut *guard;
        for SourceFileIdentifierSegment(segment) in &identifier.segments {
            module = module.submodules.entry(segment.clone()).or_default();
        }
        func(&mut module)
    }

    /// Gets a source file stored in memory, or reads it from disk if it isn't loaded yet.
    pub async fn with_source_file<F, T>(&self, identifier: &SourceFileIdentifier, func: F) -> T
    where
        F: FnOnce(Result<&SourceFile, &SourceFileLoadError>) -> T,
    {
        // To get around borrowing rules, we put the func in an option, and take it out when we use it.
        let mut func = Some(func);

        let module_identifier = &identifier.module;
        let file_identifier = &identifier.file.0;

        let result = self
            .with_module(module_identifier, |module| {
                module
                    .source_files
                    .get(file_identifier)
                    .map(|result| func.take().unwrap()(result.as_ref()))
            })
            .await;

        match result {
            Some(result) => result,
            None => {
                let file = self.load_source_file(identifier.clone()).await;
                // Recreate the borrows here, since they were implicitly destroyed so that we could clone the identifier.
                let module_identifier = &identifier.module;
                let file_identifier = &identifier.file.0;

                self.with_module(module_identifier, |module| {
                    let result = func.take().unwrap()(file.as_ref());
                    module.source_files.insert(file_identifier.clone(), file);
                    result
                })
                .await
            }
        }
    }

    async fn load_source_file(
        &self,
        identifier: SourceFileIdentifier,
    ) -> Result<SourceFile, SourceFileLoadError> {
        use tokio::io::AsyncReadExt;
        let file = File::open(
            self.directory
                .join(PathBuf::from(identifier).with_extension("quill")),
        )
        .await
        .map_err(SourceFileLoadError::IO)?;
        let metadata = file.metadata().await.map_err(SourceFileLoadError::IO)?;
        let modified_time = metadata.modified().map_err(SourceFileLoadError::IO)?;
        let mut contents = Default::default();
        BufReader::new(file)
            .read_to_string(&mut contents)
            .await
            .map_err(SourceFileLoadError::IO)?;
        Ok(SourceFile {
            contents,
            modified_time,
        })
    }
}
