use std::fs;
use std::path::Path;
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
    let file_content = fs::read_to_string(src)
        .map_err(|e| format!("Could not read {}: {}", src.as_ref().display(), e))?;

    compile_str(&file_content, dst, options)
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
            llvm_ir
                .build_bin(transmute_crt::get_crt(), dst.as_ref())
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
