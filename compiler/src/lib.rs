use std::path::{Path, PathBuf};
use std::{env, fs};
use transmute_ast::parse;
use transmute_hir::resolve;
use transmute_llvm::LlvmIrGen;
use transmute_mir::make_mir;

#[derive(Debug, Default)]
pub struct Options {
    output_format: OutputFormat,
    optimize: bool,
}

#[derive(Debug, Default)]
pub enum OutputFormat {
    #[default]
    Object,
    LlvmIr,
    Assembly,
}

impl Options {
    pub fn set_output_format(&mut self, output_format: OutputFormat) {
        self.output_format = output_format;
    }

    pub fn set_optimize(&mut self, optimize: bool) {
        self.optimize = optimize;
    }
}

pub fn compile_file<S: AsRef<Path>, D: AsRef<Path>>(
    src: &S,
    dst: &D,
    options: &Options,
) -> Result<(), String> {
    #[cfg(feature = "stdlib")]
    let source = {
        // println!("Reading {}", src.as_ref().display());
        let mut source = fs::read_to_string(src)
            .map_err(|e| format!("Could not read {}: {}", src.as_ref().display(), e))?;

        let stdlib_src =
            PathBuf::from(env::var("STDLIB_SRC_PATH").expect("STDLIB_SRC_PATH is defined"));

        for entry in fs::read_dir(&stdlib_src).unwrap() {
            let file = entry
                .expect("dir entry exists")
                .file_name()
                .to_str()
                .unwrap()
                .to_string();

            let src = stdlib_src.join(&file);
            if !src.extension().unwrap().eq("tm") {
                continue;
            }

            // println!("Reading {}", src.display());

            let src = fs::read_to_string(&src)
                .map_err(|e| format!("Could not read {}: {}", src.display(), e))?;
            source.push_str(&src);
        }

        source
    };

    #[cfg(not(feature = "stdlib"))]
    let source = {
        fs::read_to_string(src)
            .map_err(|e| format!("Could not read {}: {}", src.as_ref().display(), e))?
    };

    compile_str(&source, dst, options)
}

pub fn compile_str<S: AsRef<str>, D: AsRef<Path>>(
    src: S,
    dst: D,
    options: &Options,
) -> Result<(), String> {
    let mut ir_gen = LlvmIrGen::default();
    ir_gen.set_optimize(options.optimize);

    let llvm_ir = parse(src.as_ref())
        .and_then(resolve)
        .and_then(make_mir)
        .and_then(|mir| ir_gen.gen(&mir))
        .map_err(|d| d.to_string())?;

    match options.output_format {
        OutputFormat::Object => {
            #[cfg(feature = "rt-c")]
            let runtime = transmute_crt::get_crt();

            #[cfg(feature = "runtime")]
            let runtime = transmute_runtime::get_runtime();

            llvm_ir
                .build_bin(runtime, dst.as_ref())
                .map_err(|d| d.to_string())?;
        }
        OutputFormat::LlvmIr => {
            let dst = dst.as_ref().with_extension("ll");
            llvm_ir.write_ir(&dst).map_err(|d| d.to_string())?;
        }
        OutputFormat::Assembly => {
            let dst = dst.as_ref().with_extension("s");
            llvm_ir.write_assembly(&dst).map_err(|d| d.to_string())?;
        }
    }

    Ok(())
}
