use codegen::CodeGenContext;
use func::compile_function;
use inkwell::targets::{InitializationConfig, Target};
use inkwell::{context::Context, targets::FileType};
use inkwell::{module::Module, OptimizationLevel};
use inkwell::{
    passes::PassManager,
    targets::{CodeModel, RelocMode},
};
use quill_index::ProjectIndex;
use quill_mir::ProjectMIR;
use repr::{Monomorphisation, MonomorphisationParameters, MonomorphisedFunction, Representations};
use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::BufWriter,
    path::{Path, PathBuf},
    process::{Command, Output},
};

mod codegen;
mod func;
mod repr;

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

#[derive(Clone, Copy)]
pub struct TargetTriple {
    pub arch: TargetArchitecture,
    pub vendor: TargetVendor,
    pub os: TargetOS,
    pub env: Option<TargetEnvironment>,
}

impl Display for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(env) = &self.env {
            write!(f, "{}-{}-{}-{}", self.arch, self.vendor, self.os, env)
        } else {
            write!(f, "{}-{}-{}", self.arch, self.vendor, self.os)
        }
    }
}

impl Debug for TargetTriple {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self, f)
    }
}

#[derive(Clone, Copy)]
pub enum TargetArchitecture {
    X86_64,
}

impl Display for TargetArchitecture {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetArchitecture::X86_64 => "x86_64",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetVendor {
    Unknown,
    Pc,
}

impl Display for TargetVendor {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetVendor::Unknown => "unknown",
                TargetVendor::Pc => "pc",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetOS {
    Linux,
    Windows,
}

impl Display for TargetOS {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetOS::Linux => "linux",
                TargetOS::Windows => "windows",
            }
        )
    }
}

#[derive(Clone, Copy)]
pub enum TargetEnvironment {
    Gnu,
    Msvc,
}

impl Display for TargetEnvironment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                TargetEnvironment::Gnu => "gnu",
                TargetEnvironment::Msvc => "msvc",
            }
        )
    }
}

impl From<TargetTriple> for inkwell::targets::TargetTriple {
    fn from(triple: TargetTriple) -> Self {
        Self::create(&triple.to_string())
    }
}

#[derive(Debug, Clone)]
pub struct BuildInfo {
    pub target_triple: TargetTriple,
    pub build_folder: PathBuf,
}

/// Builds an LLVM module for the given input source file, outputting it in the given directory.
pub fn build(project_name: &str, mir: &ProjectMIR, index: &ProjectIndex, build_info: BuildInfo) {
    let target_triple = build_info.target_triple.into();

    let _ = std::fs::create_dir_all(&build_info.build_folder);
    let path = Path::new("out.o");

    // Output the MIR.
    {
        use std::io::Write;
        let mir_path = build_info.build_folder.join(path.with_extension("mir"));
        let f = File::create(mir_path).unwrap();
        let mut f = BufWriter::new(f);
        writeln!(f, "{}", mir).unwrap();
    }

    let context = Context::create();
    let module = context.create_module(project_name);
    module.set_triple(&target_triple);
    let codegen = CodeGenContext::new(&context, module);

    let mono = Monomorphisation::new(mir);
    let mut reprs = Representations::new(&codegen, index, mono.types);
    // Now that we've computed data type representations we can actually compile the functions.
    // First, declare them all.
    for func in &mono.functions {
        func.add_llvm_type(&codegen, &mut reprs, mir);
    }
    for func in &mono.functions {
        compile_function(&codegen, &reprs, index, mir, func.clone());
    }

    // Now introduce the main function.
    let main_func =
        codegen
            .module
            .add_function("main", codegen.context.i32_type().fn_type(&[], false), None);
    let main_block = codegen.context.append_basic_block(main_func, "entry");
    codegen.builder.position_at_end(main_block);
    codegen.builder.build_call(
        codegen
            .module
            .get_function(
                &MonomorphisedFunction {
                    func: mir.entry_point.clone(),
                    curry_steps: Vec::new(),
                    mono: MonomorphisationParameters {
                        type_parameters: Vec::new(),
                    },
                    direct: true,
                }
                .to_string(),
            )
            .unwrap(),
        &[],
        "call_main",
    );
    codegen
        .builder
        .build_return(Some(&codegen.context.i32_type().const_int(0, false)));

    let pm = PassManager::<Module>::create(&());
    pm.add_verifier_pass();
    println!("Verifying...");
    pm.run_on(&codegen.module);
    println!("Done.");

    // println!("Compiling to target machine...");

    Target::initialize_all(&InitializationConfig::default());

    let object_path = build_info.build_folder.join(path);
    let asm_path = build_info.build_folder.join(path.with_extension("asm"));
    let bc_path = build_info.build_folder.join(path.with_extension("bc"));
    let bc_opt_path = build_info.build_folder.join(path.with_extension("opt.bc"));

    let target = Target::from_name("x86-64").unwrap();
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "x86-64",
            "+avx2",
            OptimizationLevel::None,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();

    // Output the LLVM bitcode, and decompile it if we have `llvm-dis` on the system.
    codegen.module.write_bitcode_to_path(&bc_path);
    let _ = Command::new("llvm-dis")
        .arg(bc_path.to_str().unwrap())
        .status();

    let opt = PassManager::<Module>::create(&());
    opt.add_jump_threading_pass();
    opt.add_promote_memory_to_register_pass();
    opt.add_memcpy_optimize_pass();
    println!("Optimising...");
    opt.run_on(&codegen.module);
    println!("Writing bitcode, assembly, and object file...");

    codegen.module.write_bitcode_to_path(&bc_opt_path);
    let _ = Command::new("llvm-dis")
        .arg(bc_opt_path.to_str().unwrap())
        .status();

    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Assembly, &asm_path)
        .is_ok());
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &object_path)
        .is_ok());
}
