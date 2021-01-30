use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::Module;
use inkwell::targets::{InitializationConfig, Target};
use inkwell::OptimizationLevel;
use inkwell::{
    builder::Builder,
    targets::{CodeModel, RelocMode, TargetMachine, TargetTriple},
};
use inkwell::{context::Context, targets::FileType};
use std::{error::Error, io::BufWriter, path::Path, process::Command};

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
}

fn main() -> Result<(), Box<dyn Error>> {
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

    let sum = codegen
        .jit_compile_sum()
        .ok_or("Unable to JIT compile `sum`")?;

    Target::initialize_x86(&InitializationConfig::default());

    let opt = OptimizationLevel::Default;
    let reloc = RelocMode::Default;
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

    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &path)
        .is_ok());

    {
        use std::io::Write;
        // Output the CMakeLists.txt file.
        let mut cmakelists = BufWriter::new(std::fs::File::create("CMakeLists.txt").unwrap());
        writeln!(cmakelists, "cmake_minimum_required (VERSION 3.10)").unwrap();
        writeln!(cmakelists, "project (TEST)").unwrap();
        writeln!(cmakelists, "add_executable (test foo.o ../util.c)").unwrap();
    }

    let cmake_build_folder = format!("cmake_{}", host_triple);
    let _ = std::fs::create_dir(&cmake_build_folder);
    std::env::set_current_dir(&cmake_build_folder).unwrap();
    let cmake_configure = Command::new("cmake").arg("..").output().unwrap();
    assert!(cmake_configure.status.success());
    let cmake_build = Command::new("cmake")
        .arg("--build")
        .arg(".")
        .output()
        .unwrap();
    assert!(cmake_build.status.success());
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
        Command::new("Debug/test.exe")
    }
    #[cfg(unix)]
    {
        Command::new("./test")
    }
}
