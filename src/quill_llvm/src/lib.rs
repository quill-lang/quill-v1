use inkwell::targets::{InitializationConfig, Target};
use inkwell::{context::Context, targets::FileType};
use inkwell::{module::Module, OptimizationLevel};
use inkwell::{
    passes::PassManager,
    targets::{CodeModel, RelocMode},
};
use quill_mir::ProjectMIR;
use quill_target::{BuildInfo, TargetTriple};
use repr::Representations;
use std::{
    error::Error,
    fmt::{Debug, Display},
    fs::File,
    io::BufWriter,
    path::Path,
    process::Output,
};

use crate::monomorphisation::{
    Monomorphisation, MonomorphisationParameters, MonomorphisedFunction,
};

mod codegen;
mod debug;
mod func;
mod intrinsics;
mod monomorphisation;
mod repr;
mod sort_types;

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
pub fn build(project_name: &str, mir: &ProjectMIR, build_info: BuildInfo) {
    let target_triple = convert_triple(build_info.target_triple);

    let _ = std::fs::create_dir_all(&build_info.build_folder);
    let path = Path::new("out.o");

    // Output the project MIR.
    if build_info.emit_project_mir {
        println!("status emitting project mir");
        use std::io::Write;
        let mir_path = build_info.build_folder.join(path.with_extension("mir"));
        let f = File::create(mir_path).unwrap();
        let mut f = BufWriter::new(f);
        writeln!(f, "{}", mir).unwrap();
    }

    println!("status generating llvm context");

    let context = Context::create();
    let module = context.create_module(project_name);
    module.set_triple(&target_triple);
    let codegen = codegen::CodeGenContext::new(
        build_info.target_triple,
        &context,
        module,
        build_info.code_folder.clone(),
    );

    println!("status monomorphising");

    let mono = Monomorphisation::new(mir);
    let mut reprs = Representations::new(&codegen, &mir.index, mono.types, mono.aspects);
    // Now that we've computed data type representations we can actually compile the functions.
    // First, declare them all.
    for func in &mono.functions {
        func.add_llvm_type(&codegen, &mut reprs, mir);
    }
    reprs.create_debug_info();
    codegen.di_builder.finalize();

    println!("status compiling functions");

    for func in &mono.functions {
        func::compile_function(&codegen, &reprs, mir, func.clone());
    }

    println!("status compiling glue");

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
                    mono: MonomorphisationParameters::new(Vec::new()),
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

    let target_folder = build_info
        .build_folder
        .join(build_info.target_triple.to_string());
    let _ = std::fs::create_dir(&target_folder);

    let object_path = target_folder.join(path);
    let asm_path = target_folder.join(path.with_extension("asm"));
    let bc_path = target_folder.join(path.with_extension("basic.bc"));
    let bc_opt_path = target_folder.join(path.with_extension("bc"));
    let ll_unverified_path = target_folder.join(path.with_extension("unverified.ll"));

    if build_info.emit_unverified_llvm_ir {
        // We print twice here because it's useful to see the output if finalize fails.
        println!("status emitting unverified llvm ir (1)");
        codegen.module.print_to_file(&ll_unverified_path).unwrap();
    }
    println!("status finalising llvm ir");
    codegen.di_builder.finalize();
    if build_info.emit_unverified_llvm_ir {
        println!("status emitting unverified llvm ir (2)");
        codegen.module.print_to_file(&ll_unverified_path).unwrap();
    }

    println!("status verifying llvm ir");

    let pm = PassManager::<Module>::create(&());
    pm.add_verifier_pass();
    pm.run_on(&codegen.module);

    println!("status initialising target machine");

    Target::initialize_all(&InitializationConfig::default());

    let target = Target::from_triple(&target_triple).unwrap();
    let target_machine = target
        .create_target_machine(
            &target_triple,
            "",
            "", //"+avx2", // This was included from the tutorial.
            OptimizationLevel::None,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .unwrap();

    if build_info.emit_basic_llvm_ir {
        // Output the LLVM bitcode and IR.
        println!("status emitting basic llvm ir");
        codegen.module.write_bitcode_to_path(&bc_path);
        codegen
            .module
            .print_to_file(bc_path.with_extension("ll"))
            .unwrap();
    }

    println!("status optimising llvm ir");

    let opt = PassManager::<Module>::create(&());
    opt.add_jump_threading_pass();
    // These steps optimise, but make the LLVM IR very unreadable.
    // opt.add_scalar_repl_aggregates_pass_ssa();
    // opt.add_demote_memory_to_register_pass();
    opt.add_memcpy_optimize_pass();
    opt.add_function_attrs_pass();
    // println!("Optimising...");
    opt.run_on(&codegen.module);
    // println!("Writing bitcode, assembly, and object file...");

    if build_info.emit_llvm_ir {
        println!("status emitting llvm ir");
        codegen.module.write_bitcode_to_path(&bc_opt_path);
        codegen
            .module
            .print_to_file(bc_opt_path.with_extension("ll"))
            .unwrap();
    }

    if build_info.emit_asm {
        println!("status compiling to target machine (assembly)");
        assert!(target_machine
            .write_to_file(&codegen.module, FileType::Assembly, &asm_path)
            .is_ok());
    }

    println!("status compiling to target machine");
    assert!(target_machine
        .write_to_file(&codegen.module, FileType::Object, &object_path)
        .is_ok());
}
