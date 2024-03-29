//! Inside the compiler, types may have certain suffixes to declare what information they contain and where they should be used:
//! - `P`: just been Parsed, no extra information has been deduced.
//!   No type has been deduced, and no effort has been made to ensure syntactic correctness
//!   past the (lenient) parser.
//! - `C`: an intermediate data Cache, used when we're still in the middle of computing the index.
//!   After the index has been computed, we should not need to use `P` or `C` data,
//!   only `I` data should be required. This type suffix is *internal to the `quill_index` crate*.
//! - `I`: an Index entry for the item.
//! - `T`: currently being type checked.
//! - `M`: part of the MIR intermediate representation.
//! - (no suffix): types have been deduced and references have been resolved.

use std::{
    collections::BTreeMap,
    fmt::Display,
    io::{BufRead, BufReader},
    path::{Path, PathBuf},
    process::{Command, Stdio},
    time::{Duration, Instant},
};

use clap::{value_t, values_t, ArgMatches};
use console::style;
use indicatif::ProgressStyle;
use quill_common::{
    diagnostic::{Diagnostic, ErrorMessage, Severity},
    location::{Location, SourceFileIdentifier, SourceFileType},
};
use quill_error::ErrorEmitter;
use quill_source_file::PackageFileSystem;
use quill_target::{
    BuildInfo, TargetArchitecture, TargetEnvironment, TargetOS, TargetTriple, TargetVendor,
};
use quillc_api::{ProjectInfo, QuillcInvocation};
use tracing::{info, Level};
use tracing_subscriber::FmtSubscriber;

mod cli;
mod update;

pub struct CliConfig {
    verbose: bool,
    compiler_location: CompilerLocation,
}

/// CLI flags for the `build` or `run` command.
pub struct BuildConfig {
    timed: bool,
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum HostType {
    Linux,
    Windows,
}

impl HostType {
    /// Make the file have the right extension to be an executable on this platform.
    /// On windows, this adds the `.exe` extension.
    pub fn as_executable<P: AsRef<Path>>(&self, path: P) -> PathBuf {
        match self {
            HostType::Linux => path.as_ref().to_owned(),
            HostType::Windows => path.as_ref().with_extension("exe"),
        }
    }

    /// Returns the component name prefix assigned to this host.
    /// Returns `ubuntu-latest` for Linux, `windows-latest` for Windows.
    pub fn component_prefix(&self) -> &'static str {
        match self {
            HostType::Linux => "ubuntu-latest",
            HostType::Windows => "windows-latest",
        }
    }
}

/// Where is the Quill compiler stored?
/// By default, `quillc` and related tools are installed by the `quill` program, so it knows where to find them.
/// If we're running `quill` directly from `cargo`, we might instead want to use `cargo` to run `quillc`.
enum CompilerLocation {
    /// Runs the `quillc` whose source is in the given folder, by using `cargo`.
    Cargo { source: PathBuf },
    /// The root dir contains `compiler-deps` and a folder for each component e.g. `quillc`, `quill_lsp`.
    /// If the host is windows, a `.exe` file extension is appended to executables.
    Installed { host: HostType, root: PathBuf },
}

lazy_static::lazy_static! {
    static ref SPINNER_TEMPLATE: String = format!(
        "[{}] {} {}: {}",
        "{elapsed}",
        style("{spinner}").black().bright(),
        "{prefix}",
        style("{msg}").bright()
    );
}

/// Like [indicatif::HumanDuration], but can also format small times like milliseconds and microseconds,
/// and with two significant orders of magnitude.
/// Also colours long durations.
struct HumanSmallDuration(Duration);

impl Display for HumanSmallDuration {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.0 >= Duration::from_secs(60) {
            let secs = self.0.as_secs();
            write!(
                f,
                "{}",
                style(format!("{} min {} s", secs / 60, secs % 60))
                    .red()
                    .bold()
                    .bright()
            )
        } else if self.0 >= Duration::from_secs(1) {
            write!(
                f,
                "{}",
                style(format!(
                    "{} s {} ms",
                    self.0.as_secs(),
                    self.0.subsec_millis()
                ))
                .red()
            )
        } else if self.0 >= Duration::from_millis(1) {
            let micros = self.0.subsec_micros();
            let str = format!("{} ms {} μs", micros / 1000, micros % 1000);
            if micros > 100_000 {
                write!(f, "{}", style(str).yellow())
            } else {
                write!(f, "{}", str)
            }
        } else {
            write!(f, "{} μs", self.0.subsec_micros())
        }
    }
}

impl CompilerLocation {
    fn invoke_quillc(
        &self,
        cli_config: &CliConfig,
        build_config: &BuildConfig,
        project_config: &ProjectConfig,
        invocation: &QuillcInvocation,
    ) {
        let json = serde_json::to_string(invocation).unwrap();
        let mut command = match self {
            CompilerLocation::Cargo { source } => {
                let mut command = Command::new("cargo");
                command.current_dir(source);
                command.arg("run");

                #[cfg(not(debug_assertions))]
                command.arg("--release");

                command.arg("--bin");
                command.arg("quillc");
                if !cli_config.verbose {
                    command.arg("-q");
                }
                command.arg("--");
                command
            }
            CompilerLocation::Installed { host, root } => {
                Command::new(host.as_executable(root.join("quillc").join("quillc")))
            }
        };
        info!("JSON was {}", json);
        command.arg(json);
        command.stdout(Stdio::piped());
        command.stderr(Stdio::inherit());

        // Keep track of the time taken for each status message to be sent.
        let mut last_status = Instant::now();
        let mut current_status = None;
        let mut status_times = Vec::new();

        let mut spawned = command.spawn().unwrap();

        // Messages are given to stdout.
        let stdout = BufReader::new(spawned.stdout.take().unwrap()).lines();

        // Make a progress bar.
        let progress = indicatif::ProgressBar::new_spinner()
            .with_style(ProgressStyle::default_spinner().template(&SPINNER_TEMPLATE));
        progress.set_prefix(format!(
            "{} {}",
            style("compiling").green(),
            project_config.project_info.name
        ));
        // TODO: re-enable this with a guard so that it doesn't print anything while
        // we're emitting messages.
        //progress.enable_steady_tick(50);

        let fs = PackageFileSystem::new({
            let mut map = BTreeMap::new();
            map.insert(
                project_config.project_info.name.clone(),
                invocation.build_info.code_folder.clone(),
            );
            map
        });
        let error_emitter = ErrorEmitter::new(&fs);

        for line in stdout {
            let line = line.unwrap();
            if let Some(status) = line.strip_prefix("status ") {
                // This is a quillc status message.
                progress.set_message(status.to_owned());
                if build_config.timed {
                    let now = Instant::now();
                    let duration = now - last_status;
                    last_status = now;
                    if let Some(current_status) = current_status.take() {
                        status_times.push((current_status, duration));
                    }
                    current_status = Some(status.to_owned());
                }
            } else if let Some(message) = line.strip_prefix("message ") {
                let message: ErrorMessage = serde_json::from_str(message).unwrap();
                error_emitter.emit(message);
            } else {
                // This is just a typical user-facing message.
                println!("{}", line);
            }
        }

        let status = spawned.wait().unwrap();

        progress.finish_with_message("done");

        if build_config.timed {
            let now = Instant::now();
            let duration = now - last_status;
            if let Some(current_status) = current_status.take() {
                status_times.push((current_status, duration));
            }

            // Report the time taken for each status.
            println!("{}", style("time taken:").bright().bold());
            for (status, duration) in status_times {
                println!(" • {}: {}", status, HumanSmallDuration(duration));
            }
        }

        if !status.success() {
            std::process::exit(1);
        }
    }

    /// Where is the Zig compiler associated with this Quill compiler stored?
    fn zig_compiler(&self) -> PathBuf {
        match self {
            CompilerLocation::Cargo { .. } => {
                // Use the system Zig installation.
                PathBuf::from("zig")
            }
            CompilerLocation::Installed { root, .. } => root
                .join("compiler-deps")
                .canonicalize()
                .unwrap()
                .join("zig")
                .join("zig"),
        }
    }
}

struct ProjectConfig {
    code_folder: PathBuf,
    build_folder: PathBuf,
    project_info: ProjectInfo,
}

fn error<S: Display>(message: S) -> ! {
    println!("{} {}", console::style("error:").red().bright(), message);
    std::process::exit(1);
}

fn exit(emitter: ErrorEmitter<'_>, error_message: ErrorMessage) -> ! {
    emitter.emit(error_message);
    std::process::exit(1)
}

fn main() {
    let args = cli::gen_cli().get_matches();

    let cli_config = gen_cli_config(&args);

    match args.subcommand() {
        ("build", Some(sub_args)) => {
            process_build(&cli_config, &gen_project_config(&args), sub_args)
        }
        ("run", Some(sub_args)) => process_run(&cli_config, &gen_project_config(&args), sub_args),
        ("update", Some(sub_args)) => update::process_update(&cli_config, sub_args),
        ("clean", Some(sub_args)) => {
            process_clean(&cli_config, &gen_project_config(&args), sub_args)
        }
        ("help", _) => {
            cli::gen_cli().print_long_help().unwrap();
            println!();
        }
        _ => {
            cli::gen_cli().print_help().unwrap();
            println!();
        }
    }
}

fn gen_cli_config(args: &ArgMatches) -> CliConfig {
    let verbose = args.is_present("verbose");

    let log_level = if verbose { Some(Level::TRACE) } else { None };
    if let Some(log_level) = log_level {
        let subscriber = FmtSubscriber::builder().with_max_level(log_level).finish();
        tracing::subscriber::set_global_default(subscriber).unwrap();
        info!("initialised logging with verbosity level {}", log_level);
    }

    let compiler_location = if args.is_present("source") {
        // Find where the root directory of the `quill` source code is.
        let mut compiler_location_path: PathBuf = Path::new(".").into();
        while compiler_location_path.is_dir()
            && !compiler_location_path.join("Cargo.lock").is_file()
        {
            compiler_location_path = compiler_location_path.join("..");
        }
        CompilerLocation::Cargo {
            source: compiler_location_path,
        }
    } else {
        CompilerLocation::Installed {
            host: if cfg!(windows) {
                HostType::Windows
            } else {
                HostType::Linux
            },
            root: dirs::home_dir().unwrap().join(".quill"),
        }
    };

    CliConfig {
        verbose,
        compiler_location,
    }
}

fn gen_project_config(args: &ArgMatches<'_>) -> ProjectConfig {
    let provided_code_folder = args
        .value_of_os("project")
        .map_or_else(|| Path::new("."), Path::new);

    let code_folder = if let Ok(code_folder) = provided_code_folder.canonicalize() {
        code_folder
    } else {
        error(format!(
            "project folder '{}' did not exist",
            args.value_of_os("project")
                .map_or(".".to_string(), |os_str| os_str.to_string_lossy().into())
        ))
    };

    // Check that the code folder contains a `quill.toml` file.
    // TODO check parent directories to see if we're in a subfolder of a Quill project.

    let dummy_fs = PackageFileSystem::new(BTreeMap::new());

    let project_info = if let Ok(project_config_str) = std::fs::read(code_folder.join("quill.toml"))
    {
        match std::str::from_utf8(&project_config_str) {
            Ok(project_config_str) => {
                dummy_fs.overwrite_source_file(
                    SourceFileIdentifier {
                        module: vec![].into(),
                        file: "quill".into(),
                        file_type: SourceFileType::Toml,
                    },
                    project_config_str.to_string(),
                );
                match toml::from_str::<ProjectInfo>(project_config_str) {
                    Ok(toml) => toml,
                    Err(err) => {
                        let (line, col) = err.line_col().unwrap_or((0, 0));
                        exit(
                            ErrorEmitter::new(&dummy_fs),
                            ErrorMessage::new(
                                format!("'quill.toml' contained an error: {}", err),
                                Severity::Error,
                                Diagnostic::at_location(
                                    &SourceFileIdentifier {
                                        module: vec![].into(),
                                        file: "quill".into(),
                                        file_type: SourceFileType::Toml,
                                    },
                                    Location {
                                        line: line as u32,
                                        col: col as u32,
                                    },
                                ),
                            ),
                        )
                    }
                }
            }
            Err(err) => {
                let (valid, after_valid) = project_config_str.split_at(err.valid_up_to());
                let safe_str = unsafe { std::str::from_utf8_unchecked(valid) };
                let safe_str_chars = safe_str.chars().collect::<Vec<_>>();
                let safe_str_slice: String = safe_str_chars
                    [std::cmp::max(20, safe_str_chars.len()) - 20..]
                    .iter()
                    .collect();
                exit(
                    ErrorEmitter::new(&dummy_fs),
                    ErrorMessage::new(
                        format!(
                        "'quill.toml' contained invalid UTF-8 after '...{}', bytes were {:02X?}",
                        safe_str_slice,
                        &after_valid[..std::cmp::min(10, after_valid.len())]
                    ),
                        Severity::Error,
                        Diagnostic::in_file(&SourceFileIdentifier {
                            module: vec![].into(),
                            file: "quill".into(),
                            file_type: SourceFileType::Toml,
                        }),
                    ),
                )
            }
        }
    } else {
        exit(
            ErrorEmitter::new(&dummy_fs),
            ErrorMessage::new(
                "'quill.toml' file could not be found".to_string(),
                Severity::Error,
                Diagnostic::in_file(&SourceFileIdentifier {
                    module: vec![].into(),
                    file: "quill".into(),
                    file_type: SourceFileType::Toml,
                }),
            ),
        )
    };

    std::fs::create_dir_all(code_folder.join("build")).unwrap();
    let build_folder = code_folder.join("build").canonicalize().unwrap();

    ProjectConfig {
        code_folder,
        build_folder,
        project_info,
    }
}

fn parse_build_target(target: cli::BuildTarget) -> TargetTriple {
    match target {
        cli::BuildTarget::Win => TargetTriple {
            arch: TargetArchitecture::X86_64,
            vendor: TargetVendor::Pc,
            os: TargetOS::Windows,
            env: Some(TargetEnvironment::Gnu),
        },
        cli::BuildTarget::Linux => TargetTriple {
            arch: TargetArchitecture::X86_64,
            vendor: TargetVendor::Unknown,
            os: TargetOS::Linux,
            env: Some(TargetEnvironment::Gnu),
        },
        cli::BuildTarget::Wasm32 => TargetTriple::wasm32_wasi(),
    }
}

fn process_build(cli_config: &CliConfig, project_config: &ProjectConfig, args: &ArgMatches<'_>) {
    let targets = values_t!(args.values_of("target"), cli::BuildTarget)
        .map(|vec| vec.into_iter().map(parse_build_target).collect::<Vec<_>>())
        .unwrap_or_else(|_| vec![TargetTriple::default_triple()]);

    let build_config = generate_build_config(args);

    for target_triple in targets {
        let build_info = generate_build_info(target_triple, project_config, args);
        build(cli_config, &build_config, project_config, build_info);
    }
}

fn process_run(cli_config: &CliConfig, project_config: &ProjectConfig, args: &ArgMatches<'_>) {
    let build_config = generate_build_config(args);
    let build_info = generate_build_info(TargetTriple::default_triple(), project_config, args);
    run(cli_config, &build_config, project_config, build_info);
}

fn process_clean(_cli_config: &CliConfig, project_config: &ProjectConfig, _args: &ArgMatches<'_>) {
    let _ = std::fs::remove_dir_all(&project_config.build_folder);
}

/// Generates the build config that `quill` needs, that we do *not* send to `quillc`.
fn generate_build_config(args: &ArgMatches) -> BuildConfig {
    let timed = args.is_present("timed");
    BuildConfig { timed }
}

/// Generates the build config that `quillc` needs, but that `quill` does not.
fn generate_build_info(
    target_triple: TargetTriple,
    project_config: &ProjectConfig,
    args: &ArgMatches,
) -> BuildInfo {
    let optimisation_type = value_t!(args.value_of("opt"), cli::OptimisationType)
        .unwrap_or_else(|e| e.exit())
        .into();
    BuildInfo {
        target_triple,
        code_folder: project_config.code_folder.clone(),
        build_folder: project_config.build_folder.clone(),
        optimisation_type,

        emit_hir: args.is_present("emit-hir") || args.is_present("debug-compiler"),
        emit_mir: args.is_present("emit-mir") || args.is_present("debug-compiler"),
        emit_project_mir: args.is_present("emit-project-mir") || args.is_present("debug-compiler"),
        emit_unverified_llvm_ir: args.is_present("emit-unverified-llvm-ir")
            || args.is_present("debug-compiler"),
        emit_basic_llvm_ir: args.is_present("emit-basic-llvm-ir")
            || args.is_present("debug-compiler"),
        emit_llvm_ir: args.is_present("emit-llvm-ir") || args.is_present("debug-compiler"),
        emit_asm: args.is_present("emit-asm") || args.is_present("debug-compiler"),
    }
}

fn build(
    cli_config: &CliConfig,
    build_config: &BuildConfig,
    project_config: &ProjectConfig,
    build_info: BuildInfo,
) {
    cli_config.compiler_location.invoke_quillc(
        cli_config,
        build_config,
        project_config,
        &QuillcInvocation {
            build_info,
            zig_compiler: cli_config.compiler_location.zig_compiler(),
        },
    );
}

fn run(
    cli_config: &CliConfig,
    build_config: &BuildConfig,
    project_config: &ProjectConfig,
    build_info: BuildInfo,
) {
    build(cli_config, build_config, project_config, build_info.clone());
    let mut command = Command::new(build_info.executable(&project_config.project_info.name));
    command.current_dir(build_info.code_folder);
    let status = command.status().unwrap();
    if !status.success() {
        if let Some(code) = status.code() {
            error(format!("program terminated with error code {}", code))
        } else {
            error("program terminated with error")
        }
    }
}
