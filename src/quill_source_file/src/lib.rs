use std::{
    collections::{hash_map::Entry, HashMap},
    fmt::Debug,
    path::PathBuf,
    time::SystemTime,
};

use quill_common::{
    diagnostic::{Diagnostic, DiagnosticResult, ErrorMessage, HelpType, Severity},
    location::{ModuleIdentifier, SourceFileIdentifier, SourceFileIdentifierSegment},
};
use tokio::{fs::File, io::BufReader, sync::RwLock};

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
    pub fn new(project_directories: HashMap<String, PathBuf>) -> Self {
        Self {
            project_directories,
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

    /// Removes the cached entry of this source file from memory.
    /// Next time we need this file, it will be reloaded from disk.
    pub async fn remove_cache(&self, identifier: &SourceFileIdentifier) {
        let module_identifier = &identifier.module;
        let file_identifier = &identifier.file.0;
        self.with_module(module_identifier, |module| {
            module.source_files.remove(file_identifier)
        })
        .await;
    }

    /// Overwrites the truth of this source file with new contents.
    pub async fn overwrite_source_file(&self, identifier: SourceFileIdentifier, contents: String) {
        let module_identifier = &identifier.module;
        let file_identifier = identifier.file.0;
        self.with_module(module_identifier, |module| {
            match module.source_files.entry(file_identifier) {
                Entry::Occupied(mut occupied) => {
                    *occupied.get_mut() = Ok(SourceFile {
                        contents,
                        modified_time: SystemTime::now(),
                    });
                }
                Entry::Vacant(vacant) => {
                    vacant.insert(Ok(SourceFile {
                        contents,
                        modified_time: SystemTime::now(),
                    }));
                }
            }
        })
        .await;
    }

    async fn load_source_file(
        &self,
        identifier: SourceFileIdentifier,
    ) -> Result<SourceFile, SourceFileLoadError> {
        use tokio::io::AsyncReadExt;
        let directory = self.project_directories[&identifier.module.segments[0].0].clone();
        let directory = identifier
            .module
            .segments
            .iter()
            .skip(1)
            .fold(directory, |dir, segment| dir.join(&segment.0));

        let file = File::open(
            directory
                .join(identifier.file.0)
                .with_extension(identifier.file_type.file_extension()),
        )
        .await
        .map_err(SourceFileLoadError::Io)?;

        let metadata = file.metadata().await.map_err(SourceFileLoadError::Io)?;
        let modified_time = metadata.modified().map_err(SourceFileLoadError::Io)?;
        let mut contents = Default::default();
        BufReader::new(file)
            .read_to_string(&mut contents)
            .await
            .map_err(SourceFileLoadError::Io)?;
        Ok(SourceFile {
            contents,
            modified_time,
        })
    }
}

/// Prints error and warning messages, outputting the relevant lines of source code from the input files.
#[must_use = "error messages must be emitted using the emit_all method"]
pub struct ErrorEmitter<'fs> {
    /// The error emitter caches messages and will not output them until `emit_all` is called.
    /// This defers asynchronous (file reading) operations until after the compilation step is finished.
    /// Order of emission of the messages is preserved.
    messages: Vec<ErrorMessage>,

    /// If this is true, warnings will not be cached or emitted.
    has_emitted_error: bool,

    package_file_system: &'fs PackageFileSystem,
}

impl<'fs> ErrorEmitter<'fs> {
    pub fn new(package_file_system: &'fs PackageFileSystem) -> Self {
        Self {
            messages: Vec::new(),
            has_emitted_error: false,
            package_file_system,
        }
    }

    /// Consumes the errors of a diagnostic result, yielding the encapsulated value.
    pub fn consume_diagnostic<T>(&mut self, diagnostic_result: DiagnosticResult<T>) -> Option<T> {
        let (value, messages) = diagnostic_result.destructure();
        self.process(messages);
        value
    }

    /// Adds some messages to this error emitter.
    pub fn process(&mut self, messages: impl IntoIterator<Item = ErrorMessage>) {
        for message in messages {
            match message.severity {
                Severity::Warning => {
                    if !self.has_emitted_error {
                        self.messages.push(message);
                    }
                }
                Severity::Error => {
                    self.has_emitted_error = true;
                    self.messages.push(message);
                }
            }
        }
    }

    async fn emit(&self, message: ErrorMessage) {
        use console::style;

        match message.severity {
            Severity::Error => {
                println!(
                    "{}{} {}",
                    style("error").red().bright(),
                    style(":").white().bright(),
                    style(message.message).white().bright()
                );
                self.print_message(message.diagnostic, |s| style(s).red().bright())
                    .await;
            }
            Severity::Warning => {
                println!(
                    "{}: {}",
                    style("warning").yellow().bright(),
                    message.message
                );
                self.print_message(message.diagnostic, |s| style(s).yellow().bright())
                    .await;
            }
        }

        for help in message.help {
            match help.help_type {
                HelpType::Help => println!(
                    "{} {}",
                    style("help:").white().bright(),
                    style(help.message).white().bright()
                ),
                HelpType::Note => println!(
                    "{} {}",
                    style("note:").white().bright(),
                    style(help.message).white().bright()
                ),
            }
            self.print_message(help.diagnostic, |s| style(s).cyan().bright())
                .await;
        }
    }

    async fn print_message(
        &self,
        diagnostic: Diagnostic,
        style_arrows: impl Fn(String) -> console::StyledObject<String>,
    ) {
        use console::style;

        if let Some(range) = diagnostic.range {
            // We calculate the amount of digits in the line number.
            let line_number_max_digits =
                (range.start.line.max(range.end.line) + 1).to_string().len();

            println!(
                "{}{} {} ({}) @ {}:{}",
                " ".repeat(line_number_max_digits),
                style("-->").cyan().bright(),
                diagnostic.source_file,
                diagnostic.source_file.file_type,
                range.start.line + 1,
                range.start.col + 1
            );

            // Let's get the contents of the offending source code file.
            self.package_file_system
                .with_source_file(&diagnostic.source_file, |source_file| {
                    // We don't need to worry about optimising reads from the source file, since it's cached in memory anyway,
                    // and this is the cold path because we're just handling errors.
                    match source_file {
                        Ok(source_file) => {
                            let lines = source_file
                                .get_contents()
                                .lines()
                                .enumerate()
                                .skip(range.start.line as usize)
                                .take((range.end.line - range.start.line + 1) as usize);

                            // Print out each relevant line of code, starting and finishing with an empty line.

                            // Empty line.
                            println!(
                                "{: >2$} {}",
                                "",
                                style("|").cyan().bright(),
                                line_number_max_digits,
                            );

                            // Relevant lines.
                            for (line_number, line_contents) in lines {
                                let line_length = line_contents.chars().count();

                                // Signal where on the line the error occured if we're on the first line.
                                if line_number == range.start.line as usize {
                                    // If the error was on a single line, we'll just underline where the error occured.
                                    // We don't need an overline.
                                    if range.start.line != range.end.line {
                                        println!(
                                            "{: >4$} {} {: >5$}{}",
                                            "",
                                            style("|").cyan().bright(),
                                            "",
                                            style_arrows(
                                                "v".repeat(line_length - range.start.col as usize)
                                            ),
                                            line_number_max_digits,
                                            range.start.col as usize,
                                        );
                                    }
                                }

                                println!(
                                    "{: >3$} {} {}",
                                    style((line_number + 1).to_string()).cyan().bright(),
                                    style("|").cyan().bright(),
                                    line_contents,
                                    line_number_max_digits,
                                );

                                // Signal where on the line the error occured if we're on the last line.
                                if line_number == range.end.line as usize {
                                    if range.start.line == range.end.line {
                                        // The error was on a single line. We'll just underline where the error occured.
                                        println!(
                                            "{: >4$} {} {: >5$}{}",
                                            "",
                                            style("|").cyan().bright(),
                                            "",
                                            style_arrows("^".repeat(
                                                range.end.col as usize - range.start.col as usize
                                            )),
                                            line_number_max_digits,
                                            range.start.col as usize,
                                        );
                                    } else {
                                        // Underline from the start of the line to the end of the error.
                                        println!(
                                            "{: >3$} {} {}",
                                            "",
                                            style("|").cyan().bright(),
                                            style_arrows("^".repeat(range.end.col as usize)),
                                            line_number_max_digits,
                                        );
                                    }
                                }
                            }

                            // Empty line.
                            println!(
                                "{: >2$} {}",
                                "",
                                style("|").cyan().bright(),
                                line_number_max_digits,
                            );
                        }
                        Err(_) => {
                            println!(
                                "{}",
                                style("could not read file".to_string()).red().bright()
                            );
                        }
                    }
                })
                .await;
        } else {
            println!(
                "{} {}",
                style("-->").cyan().bright(),
                diagnostic.source_file
            );
        }
    }

    /// Displays all error and warning messages. If an error was emitted, returns true.
    /// This function may read files from the disk in order to emit a more user-friendly error message, hence it is asynchronous.
    pub async fn emit_all(mut self) -> bool {
        let messages = std::mem::take(&mut self.messages);
        for message in messages {
            if message.severity == Severity::Error || !self.has_emitted_error {
                self.emit(message).await;
            }
        }
        self.has_emitted_error
    }
}
