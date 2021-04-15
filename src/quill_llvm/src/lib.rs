#![feature(iter_intersperse)]

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
use quill_target::{BuildInfo, TargetTriple};
use repr::{Monomorphisation, MonomorphisationParameters, MonomorphisedFunction, Representations};
use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::BufWriter,
    path::Path,
    process::Output,
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

fn convert_triple(triple: TargetTriple) -> inkwell::targets::TargetTriple {
    inkwell::targets::TargetTriple::create(&triple.to_string())
}

/// Builds an LLVM module for the given input source file, outputting it in the given directory.
pub fn build(project_name: &str, mir: &ProjectMIR, index: &ProjectIndex, build_info: BuildInfo) {
    let target_triple = convert_triple(build_info.target_triple);

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
    reprs.create_drop_funcs();
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

    let object_path = build_info.build_folder.join(path);
    let asm_path = build_info.build_folder.join(path.with_extension("asm"));
    let bc_path = build_info.build_folder.join(path.with_extension("bc"));
    let bc_opt_path = build_info.build_folder.join(path.with_extension("opt.bc"));
    let ll_unverified_path = build_info
        .build_folder
        .join(path.with_extension("unverified.ll"));

    // We print twice here because it's useful to see the output if finalize fails.
    codegen.module.print_to_file(&ll_unverified_path).unwrap();
    codegen.di_builder.finalize();
    codegen.module.print_to_file(ll_unverified_path).unwrap();

    let pm = PassManager::<Module>::create(&());
    pm.add_verifier_pass();
    println!("Verifying...");
    pm.run_on(&codegen.module);
    println!("Done.");

    // println!("Compiling to target machine...");

    Target::initialize_all(&InitializationConfig::default());

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

    // Output the LLVM bitcode and IR.
    codegen.module.write_bitcode_to_path(&bc_path);
    codegen
        .module
        .print_to_file(bc_path.with_extension("ll"))
        .unwrap();

    let opt = PassManager::<Module>::create(&());
    opt.add_jump_threading_pass();
    // These steps optimise, but make the LLVM IR very unreadable.
    // opt.add_scalar_repl_aggregates_pass_ssa();
    // opt.add_demote_memory_to_register_pass();
    opt.add_memcpy_optimize_pass();
    opt.add_function_attrs_pass();
    println!("Optimising...");
    opt.run_on(&codegen.module);
    println!("Writing bitcode, assembly, and object file...");

    codegen.module.write_bitcode_to_path(&bc_opt_path);
    codegen
        .module
        .print_to_file(bc_opt_path.with_extension("ll"))
        .unwrap();

    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Assembly, &asm_path)
        .is_ok());
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &object_path)
        .is_ok());
}
