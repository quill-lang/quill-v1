use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    io::Read,
    path::{Path, PathBuf},
    time::SystemTime,
};

use quill_common::location::{
    ModuleIdentifier, SourceFileIdentifier, SourceFileIdentifierSegment, SourceFileType,
};
use std::{fs::File, io::BufReader, sync::RwLock};

/// If a source file's contents could not be loaded, why was this?
#[derive(Debug)]
pub enum SourceFileLoadError {
    Io(std::io::Error),
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
    /// Maps project names (e.g. `core`) to the path their sources (and the `quill.toml` file) are stored at.
    pub project_directories: HashMap<String, PathBuf>,
    root_module: RwLock<Module>,
}

impl PackageFileSystem {
    /// TODO: Make only one project_directories map in `quill` and send it to `quillc`.
    pub fn new(project_directories: HashMap<String, PathBuf>) -> Self {
        Self {
            project_directories,
            root_module: RwLock::new(Module::default()),
        }
    }

    fn with_module<F, T>(&self, identifier: &ModuleIdentifier, func: F) -> T
    where
        F: FnOnce(&mut Module) -> T,
    {
        let mut guard = self.root_module.write().unwrap();
        let mut module = &mut *guard;
        for SourceFileIdentifierSegment(segment) in &identifier.segments {
            module = module.submodules.entry(segment.clone()).or_default();
        }
        func(&mut module)
    }

    /// Gets a source file stored in memory, or reads it from disk if it isn't loaded yet.
    pub fn with_source_file<F, T>(&self, identifier: &SourceFileIdentifier, func: F) -> T
    where
        F: FnOnce(Result<&SourceFile, &SourceFileLoadError>) -> T,
    {
        // To get around borrowing rules, we put the func in an option, and take it out when we use it.
        let mut func = Some(func);

        let module_identifier = &identifier.module;
        let file_identifier = &identifier.file.0;

        let result = self.with_module(module_identifier, |module| {
            module
                .source_files
                .get(file_identifier)
                .map(|result| func.take().unwrap()(result.as_ref()))
        });

        match result {
            Some(result) => result,
            None => {
                let file = self.load_source_file(identifier.clone());
                // Recreate the borrows here, since they were implicitly destroyed so that we could clone the identifier.
                let module_identifier = &identifier.module;
                let file_identifier = &identifier.file.0;

                self.with_module(module_identifier, |module| {
                    let result = func.take().unwrap()(file.as_ref());
                    module.source_files.insert(file_identifier.clone(), file);
                    result
                })
            }
        }
    }

    /// Removes the cached entry of this source file from memory.
    /// Next time we need this file, it will be reloaded from disk.
    pub fn remove_cache(&self, identifier: &SourceFileIdentifier) {
        let module_identifier = &identifier.module;
        let file_identifier = &identifier.file.0;
        self.with_module(module_identifier, |module| {
            module.source_files.remove(file_identifier)
        });
    }

    /// Overwrites the truth of this source file with new contents.
    pub fn overwrite_source_file(&self, identifier: SourceFileIdentifier, contents: String) {
        // eprintln!("overwriting {}", identifier);
        let module_identifier = &identifier.module;
        let file_identifier = identifier.file.0;
        self.with_module(module_identifier, |module| {
            match module.source_files.entry(file_identifier) {
                Entry::Occupied(mut occupied) => {
                    // eprintln!("source was {:?}", occupied.get());
                    *occupied.get_mut() = Ok(SourceFile {
                        contents,
                        modified_time: SystemTime::now(),
                    });
                    // eprintln!("source now {:?}", occupied.get());
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(Ok(SourceFile {
                        contents,
                        modified_time: SystemTime::now(),
                    }));
                }
            }
        });
    }

    pub fn file_path(&self, identifier: &SourceFileIdentifier) -> PathBuf {
        let directory = self.project_directories[&identifier.module.segments[0].0].clone();
        let directory = identifier
            .module
            .segments
            .iter()
            .skip(1)
            .fold(directory, |dir, segment| dir.join(&segment.0));
        directory
            .join(&identifier.file.0)
            .with_extension(identifier.file_type.file_extension())
    }

    fn load_source_file(
        &self,
        identifier: SourceFileIdentifier,
    ) -> Result<SourceFile, SourceFileLoadError> {
        let file = File::open(self.file_path(&identifier)).map_err(SourceFileLoadError::Io)?;

        let metadata = file.metadata().map_err(SourceFileLoadError::Io)?;
        let modified_time = metadata.modified().map_err(SourceFileLoadError::Io)?;
        let mut contents = Default::default();
        BufReader::new(file)
            .read_to_string(&mut contents)
            .map_err(SourceFileLoadError::Io)?;
        Ok(SourceFile {
            contents,
            modified_time,
        })
    }
}

pub fn find_all_source_files(
    root_module: ModuleIdentifier,
    code_folder: &Path,
) -> Vec<SourceFileIdentifier> {
    let mut result = Vec::new();
    let read_dir = std::fs::read_dir(code_folder).unwrap();
    for entry in read_dir {
        let entry = entry.unwrap();
        let metadata = entry.metadata().unwrap();
        if metadata.is_file() {
            let os_fname = entry.file_name();
            let fname = os_fname.to_string_lossy();
            if let Some(fname) = fname.strip_suffix(".ql") {
                result.push(SourceFileIdentifier {
                    module: root_module.clone(),
                    file: fname.to_string().into(),
                    file_type: SourceFileType::Quill,
                })
            }
        } else if metadata.is_dir() {
            let os_folder_name = entry.file_name();
            let folder_name = os_folder_name.to_string_lossy();
            // TODO: check if this is a valid folder name.
            result.extend(find_all_source_files(
                ModuleIdentifier {
                    segments: root_module
                        .segments
                        .iter()
                        .cloned()
                        .chain(std::iter::once(folder_name.into()))
                        .collect(),
                },
                &entry.path(),
            ));
        }
    }
    result
}
