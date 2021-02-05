use console::style;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{InitializationConfig, Target};
use inkwell::AddressSpace;
use inkwell::{
    builder::Builder,
    targets::{CodeModel, RelocMode, TargetTriple},
};
use inkwell::{comdat::ComdatSelectionKind, OptimizationLevel};
use inkwell::{context::Context, targets::FileType};
use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::BufWriter,
    path::Path,
    process::{Command, Output},
};

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    fn compile_main(&self) {
        let i8_t = self.context.i8_type();
        let i32_t = self.context.i32_type();
        let i64_t = self.context.i64_type();

        let fn_type = i32_t.fn_type(
            &[
                i32_t.into(),
                i8_t.ptr_type(AddressSpace::Generic)
                    .ptr_type(AddressSpace::Generic)
                    .into(),
            ],
            false,
        );
        let function = self.module.add_function("main", fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let puts = self.module.add_function(
            "puts",
            i32_t.fn_type(&[i8_t.ptr_type(AddressSpace::Generic).into()], false),
            Some(Linkage::External),
        );
        let hello_world_message = unsafe {
            self.builder
                .build_global_string("Hello, world!", "hello_world")
        };
        let comdat = self.module.get_or_insert_comdat("hello_world");
        comdat.set_selection_kind(ComdatSelectionKind::ExactMatch);
        hello_world_message.set_comdat(comdat);
        hello_world_message.set_linkage(Linkage::LinkOnceODR);
        hello_world_message.set_constant(true);
        let hello_world_deref = unsafe {
            self.builder.build_in_bounds_gep(
                hello_world_message.as_pointer_value(),
                &[i64_t.const_int(0, false), i64_t.const_int(0, false)],
                "hello_world_deref",
            )
        };
        self.builder
            .build_call(puts, &[hello_world_deref.into()], "call");

        self.builder.build_return(Some(&i32_t.const_int(0, false)));
    }
}

struct ExecutionError {
    program: String,
    output: Output,
}

impl Error for ExecutionError {}

impl Debug for ExecutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{} failed with {}", self.program, self.output.status)?;
        writeln!(f, "Output:")?;
        writeln!(f, "{}", std::str::from_utf8(&self.output.stdout).unwrap())?;
        writeln!(f, "Error Output:")?;
        writeln!(f, "{}", std::str::from_utf8(&self.output.stderr).unwrap())?;
        Ok(())
    }
}

impl Display for ExecutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    println!("{} Building module...", style("[1/4]").bold().dim());

    let host_triple = guess_host_triple::guess_host_triple().unwrap();

    std::env::set_current_dir("test").unwrap();

    let build_folder = format!("target/{}", host_triple);
    let _ = std::fs::create_dir_all(&build_folder);
    std::env::set_current_dir(&build_folder).unwrap();

    let _ = std::fs::create_dir("bin");
    let _ = std::fs::create_dir("obj");
    let _ = std::fs::create_dir("asm");
    let _ = std::fs::create_dir("bc");

    let context = Context::create();
    let module = context.create_module("sum");
    let codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
    };

    codegen.compile_main();

    println!(
        "{} Compiling to target machine...",
        style("[2/4]").bold().dim()
    );

    Target::initialize_all(&InitializationConfig::default());

    let path = Path::new("foo.o");
    let object_path = Path::new("obj/").join(path);
    let asm_path = Path::new("asm/").join(path.with_extension("asm"));
    let bc_path = Path::new("bc/").join(path.with_extension("bc"));

    let target = Target::from_name("x86-64").unwrap();
    let target_machine = target
        .create_target_machine(
            &TargetTriple::create(host_triple),
            "x86-64",
            "+avx2",
            OptimizationLevel::Default,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();

    // Output the LLVM bitcode, and decompile it if we have `llvm-dis` on the system.
    codegen.module.write_bitcode_to_path(&bc_path);
    let _ = Command::new("llvm-dis")
        .arg(bc_path.to_str().unwrap())
        .status();
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Assembly, &asm_path)
        .is_ok());
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &object_path)
        .is_ok());

    // Create a "glue" file to force CMake to use the C linker and actually link libc, instead of whatever it normally does.
    File::create(Path::new("obj/glue.c")).unwrap();

    println!("{} Configuring CMake...", style("[3/4]").bold().dim());

    {
        use std::io::Write;
        // Output the CMakeLists.txt file.
        let mut cmakelists = BufWriter::new(std::fs::File::create("obj/CMakeLists.txt").unwrap());
        writeln!(cmakelists, "cmake_minimum_required (VERSION 3.10)").unwrap();
        writeln!(cmakelists, "project (TEST)").unwrap();
        writeln!(cmakelists, "add_executable (test foo.o glue.c)").unwrap();
    }

    std::env::set_current_dir("bin").unwrap();

    let cmake_configure = Command::new("cmake").arg("../obj").output().unwrap();
    if !cmake_configure.status.success() {
        return Err(Box::new(ExecutionError {
            program: "cmake configure".to_owned(),
            output: cmake_configure,
        }));
    }

    println!("{} Linking...", style("[4/4]").bold().dim());

    let cmake_build = Command::new("cmake")
        .arg("--build")
        .arg(".")
        .output()
        .unwrap();
    if !cmake_build.status.success() {
        return Err(Box::new(ExecutionError {
            program: "cmake build".to_owned(),
            output: cmake_build,
        }));
    }

    println!(
        "{} Running executable...",
        style("Complete!").bold().green()
    );
    assert!(run_executable().status().unwrap().success());

    // let x = 1u64;
    // let y = 2u64;
    // let z = 3u64;

    // unsafe {
    //     println!("{} + {} + {} = {}", x, y, z, sum.call(x, y, z));
    //     assert_eq!(sum.call(x, y, z), x + y + z);
    // }

    Ok(())
}

fn run_executable() -> Command {
    #[cfg(windows)]
    {
        Command::new("./Debug/test.exe")
    }
    #[cfg(unix)]
    {
        Command::new("./test")
    }
}
