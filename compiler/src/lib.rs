use std::borrow::Cow;
use std::fs;
use std::path::{Path, PathBuf};
use transmute_ast::parse;
use transmute_hir::resolve;
use transmute_llvm::LlvmIrGen;
use transmute_mir::make_mir;

#[derive(Debug, Default)]
pub struct Options {
    output_format: OutputFormat,
    optimize: bool,
    stdlib_path: Option<PathBuf>,
}

#[derive(Debug, Default)]
pub enum OutputFormat {
    #[default]
    Object,
    LlvmIr,
    Assembly,
    Source,
}

impl Options {
    pub fn set_output_format(&mut self, output_format: OutputFormat) {
        self.output_format = output_format;
    }

    pub fn set_optimize(&mut self, optimize: bool) {
        self.optimize = optimize;
    }

    pub fn set_stdlib_path(&mut self, stdlib_path: PathBuf) {
        self.stdlib_path = Some(stdlib_path);
    }
}

pub fn compile_file<S: AsRef<Path>, D: AsRef<Path>>(
    src: &S,
    dst: &D,
    options: &Options,
) -> Result<(), String> {
    let mut source = fs::read_to_string(src)
        .map_err(|e| format!("Could not read {}: {}", src.as_ref().display(), e))?;

    source.push_str(read_stdlib_src(options)?.as_ref());

    #[cfg(feature = "gc-functions")]
    source.push_str(include_str!("gc-functions.tm"));

    if matches!(options.output_format, OutputFormat::Source) {
        println!("{source}");
        Ok(())
    } else {
        compile_str(&source, dst, options)
    }
}

fn read_stdlib_src(options: &Options) -> Result<Cow<str>, String> {
    Ok(match options.stdlib_path.as_ref() {
        None => Cow::Borrowed(""),
        Some(stdlib_path) => {
            let mut source = String::new();
            let stdlib_src = stdlib_path.join("src");
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
                source.push_str(&format!("\n\n#-- {file} --------------------\n"));
                source.push_str(&src);
            }
            Cow::Owned(source)
        }
    })
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
                .build_bin(
                    transmute_runtime::get_runtime(),
                    dst.as_ref(),
                    options.stdlib_path.as_deref(),
                )
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
        OutputFormat::Source => {
            // already done
        }
    }

    Ok(())
}
