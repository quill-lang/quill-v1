use console::style;
use indicatif::ProgressBar;
use inkwell::OptimizationLevel;
use inkwell::{
    builder::Builder,
    targets::{CodeModel, RelocMode, TargetMachine, TargetTriple},
};
use inkwell::{
    comdat::Comdat,
    targets::{InitializationConfig, Target},
};
use inkwell::{context::Context, targets::FileType};
use inkwell::{
    execution_engine::{ExecutionEngine, JitFunction},
    AddressSpace,
};
use inkwell::{
    module::{Linkage, Module},
    values::PointerValue,
};
use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::BufWriter,
    path::Path,
    process::{Command, Output},
};

/// Convenience type alias for the `sum` function.
///
/// Calling this is innately `unsafe` because there's no guarantee it doesn't
/// do `unsafe` operations internally.
type SumFunc = unsafe extern "C" fn(u64, u64, u64) -> u64;

struct CodeGen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    execution_engine: ExecutionEngine<'ctx>,
}

impl<'ctx> CodeGen<'ctx> {
    fn jit_compile_sum(&self) -> Option<JitFunction<SumFunc>> {
        let i64_type = self.context.i64_type();
        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
        let function = self.module.add_function("sum", fn_type, None);
        let basic_block = self.context.append_basic_block(function, "entry");

        self.builder.position_at_end(basic_block);

        let x = function.get_nth_param(0)?.into_int_value();
        let y = function.get_nth_param(1)?.into_int_value();
        let z = function.get_nth_param(2)?.into_int_value();

        let sum = self.builder.build_int_add(x, y, "sum");
        let sum = self.builder.build_int_add(sum, z, "sum");

        self.builder.build_return(Some(&sum));

        unsafe { self.execution_engine.get_function("sum").ok() }
    }

    fn jit_compile_main(&self) -> Option<JitFunction<SumFunc>> {
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

        unsafe { self.execution_engine.get_function("sum").ok() }
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
    let _ = std::fs::create_dir("target");
    std::env::set_current_dir("target").unwrap();

    let context = Context::create();
    let module = context.create_module("sum");
    let execution_engine = module.create_jit_execution_engine(OptimizationLevel::None)?;
    let codegen = CodeGen {
        context: &context,
        module,
        builder: context.create_builder(),
        execution_engine,
    };

    //let sum = codegen
    //    .jit_compile_sum()
    //    .ok_or("Unable to JIT compile `sum`")?;

    codegen.jit_compile_sum();
    codegen.jit_compile_main();

    println!(
        "{} Compiling to target machine...",
        style("[2/4]").bold().dim()
    );

    Target::initialize_x86(&InitializationConfig::default());

    let opt = OptimizationLevel::Default;
    let reloc = RelocMode::PIC;
    let model = CodeModel::Default;
    let path = Path::new("foo.o");
    let target = Target::from_name("x86-64").unwrap();
    let target_machine = target
        .create_target_machine(
            &TargetTriple::create(host_triple),
            "x86-64",
            "+avx2",
            opt,
            reloc,
            model,
        )
        .unwrap();

    // Output the LLVM bitcode, and decompile it if we have `llvm-dis` on the system.
    codegen
        .module
        .write_bitcode_to_path(&path.with_extension("bc"));
    let _ = Command::new("llvm-dis")
        .arg(path.with_extension("bc").to_str().unwrap())
        .status();
    assert!(target_machine
        .write_to_file(
            &codegen.module,
            FileType::Assembly,
            &path.with_extension("asm")
        )
        .is_ok());
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &path)
        .is_ok());

    // Create a "glue" file to force CMake to use the C linker and actually link libc, instead of whatever it normally does.
    File::create(Path::new("glue.c")).unwrap();

    println!("{} Configuring CMake...", style("[3/4]").bold().dim());

    {
        use std::io::Write;
        // Output the CMakeLists.txt file.
        let mut cmakelists = BufWriter::new(std::fs::File::create("CMakeLists.txt").unwrap());
        writeln!(cmakelists, "cmake_minimum_required (VERSION 3.10)").unwrap();
        writeln!(cmakelists, "project (TEST)").unwrap();
        writeln!(cmakelists, "add_executable (test foo.o glue.c)").unwrap();
    }

    let cmake_build_folder = format!("cmake_{}", host_triple);
    let _ = std::fs::create_dir(&cmake_build_folder);
    std::env::set_current_dir(&cmake_build_folder).unwrap();
    let cmake_configure = Command::new("cmake").arg("..").output().unwrap();
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
