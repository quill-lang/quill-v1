use clap::*;

arg_enum! {
    #[derive(PartialEq, Debug)]
    pub enum BuildTarget {
        Win,
        Linux,
        Wasm32,
    }
}

arg_enum! {
    #[derive(PartialEq, Debug)]
    pub enum OptimisationType {
        Debug,
        ReleaseFast,
        ReleaseSafe,
        ReleaseSmall,
    }
}

impl From<OptimisationType> for quill_target::OptimisationType {
    fn from(opt: OptimisationType) -> Self {
        match opt {
            OptimisationType::Debug => Self::Debug,
            OptimisationType::ReleaseFast => Self::ReleaseFast,
            OptimisationType::ReleaseSafe => Self::ReleaseSafe,
            OptimisationType::ReleaseSmall => Self::ReleaseSmall,
        }
    }
}

/// All switches from `build` are copied into `run`.
pub fn gen_cli() -> App<'static, 'static> {
    app_from_crate!("\n")
        .setting(AppSettings::SubcommandRequiredElseHelp)
        .setting(AppSettings::InferSubcommands)
        .arg(
            Arg::with_name("project")
                .long("project")
                .short("p")
                .help("The directory that contains the Quill project")
                .value_name("DIR"),
        )
        .arg(
            Arg::with_name("verbose")
                .long("verbose")
                .short("v")
                .help("Makes the compiler emit verbose output"),
        )
        .arg(
            Arg::with_name("source")
                .long("source")
                .short("s")
                .help("Executes components of the Quill compiler from source")
                .long_help(
                    "\
                    Executes components of the Quill compiler from source. \
                    This is not intended for use outside of development of the compiler. \
                    In particular, it will try to use your system Rust installation \
                    to compile `quillc`, which is expected to be in this folder. \
                    Further, it will use the system's `zig` installation for linking \
                    instead of any `zig` that ships with Quill.\
                    ",
                ),
        )
        .subcommand(build())
        .subcommand(run())
        .subcommand(clean())
        .subcommand(update())
}

/// Adds all flags that are relevant to building a quill project.
fn build_flags(app: App<'static, 'static>) -> App<'static, 'static> {
    app.arg(
        Arg::with_name("timed")
            .long("timed")
            .short("T")
            .help("Reports the time taken for each phase of compilation to complete"),
    )
    .arg(
        Arg::with_name("opt")
            .long("opt")
            .short("O")
            .value_name("MODE")
            .help("Choose whether to optimise, and what to optimise for")
            .possible_values(&OptimisationType::variants())
            .case_insensitive(true)
            .default_value("Debug"),
    )

    .arg(
        Arg::with_name("emit-hir")
            .long("emit-hir")
            .help("Emits HIR for each file")
            .long_help("Emits the HIR (high level intermediate representation) representation of each file to build/ir/<file>.hir"),
    )
    .arg(
        Arg::with_name("emit-mir")
            .long("emit-mir")
            .help("Emits MIR for each file")
            .long_help("Emits the MIR (mid level intermediate representation) representation of each file to build/ir/<file>.mir"),
    )
    .arg(
        Arg::with_name("emit-project-mir")
            .long("emit-project-mir")
            .help("Emits MIR for entire project")
            .long_help("Emits the MIR representation of the entire project to build/out.mir"),
    )
    .arg(
        Arg::with_name("emit-unverified-llvm-ir")
            .long("emit-unverified-llvm-ir")
            .help("Emits unverified LLVM IR")
            .long_help("Emits the compiled LLVM IR to build/out.unverified.ll"),
    )
    .arg(
        Arg::with_name("emit-basic-llvm-ir")
            .long("emit-basic-llvm-ir")
            .help("Emits basic LLVM IR")
            .long_help("Emits the compiled LLVM IR to build/out.basic.ll after verifying that the module is valid, but before LLVM optimises it at all"),
    )
    .arg(
        Arg::with_name("emit-llvm-ir")
            .long("emit-llvm-ir")
            .help("Emit LLVM IR")
            .long_help("Emits the compiled LLVM IR to build/out.ll after LLVM's optimisation passes, which may make the IR almost unreadable; \
            see --emit-basic-llvm-ir for a logically identical but more readable IR"),
    )
    .arg(
        Arg::with_name("emit-asm")
            .long("emit-asm")
            .help("Emits target-specific assembly")
            .long_help("Emits the target-specific assembly to build/out.asm"),
    )

    .arg(
        Arg::with_name("debug-compiler")
            .long("debug-compiler")
            .help("Emits all intermediate representations for debugging the compiler's output")
            .long_help("Emits all intermediate representations for debugging the compiler's output; \
            implies --emit-hir, --emit-mir, --emit-project-mir, --emit-unverified-llvm-ir, --emit-basic-llvm-ir, --emit-llvm-ir, --emit-asm"),
    )
}

fn build() -> App<'static, 'static> {
    let app = App::new("build")
        .about("Builds the Quill code in a given folder into an executable file")
        .arg(
            Arg::with_name("target")
                .long("target")
                .short("t")
                .multiple(true)
                .value_name("TARGET")
                .help("Specifies a target to compile code for, if none are provided it compiles for the host system")
                .possible_values(&BuildTarget::variants())
                .case_insensitive(true)
        );
    build_flags(app)
}

fn run() -> App<'static, 'static> {
    let app = App::new("run").about("Runs the Quill code in a given folder");
    build_flags(app)
}

fn clean() -> App<'static, 'static> {
    App::new("clean").about("Removes all build files").long_about("Removes all build files so that the project will be guaranteed to be built from scratch next time")
}

fn update() -> App<'static, 'static> {
    App::new("update").about("Updates the Quill compiler and its dependencies")
}
