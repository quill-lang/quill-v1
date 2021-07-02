use clap::*;

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
                .long_help(
                    "\
                    Specifies a target to compile code for, if none are provided it compiles for the host system.\n\
                    Supported targets: win, linux, wasm32\
                    ")
        );
    build_flags(app)
}

fn run() -> App<'static, 'static> {
    let app = App::new("run").about("Runs the Quill code in a given folder");
    build_flags(app)
}

fn update() -> App<'static, 'static> {
    App::new("update").about("Updates the Quill compiler and its dependencies")
}
