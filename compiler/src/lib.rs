use std::path::{Path, PathBuf};
use transmute_ast::ast_print::Options as AstPrintOptions;
use transmute_ast::parse;
use transmute_core::error::Diagnostics;
use transmute_core::input::Input;
use transmute_hir::hir_print::Options as HirPrintOptions;
use transmute_hir::Resolve;
use transmute_llvm::{LlvmIr, LlvmIrGen};
use transmute_mir::Mir;
use transmute_nst::nodes::Nst;

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
    Ast,
    Hir,
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
    #[cfg(not(feature = "gc-functions"))]
    let mut inputs = vec![Input::core(), Input::try_from(PathBuf::from(src.as_ref()))?];

    #[cfg(feature = "gc-functions")]
    let mut inputs = vec![
        Input::core(),
        Input::from(("gc-functions", include_str!("gc-functions.tm"))),
        Input::try_from(PathBuf::from(src.as_ref()))?,
    ];

    if let Some(stdlib_path) = &options.stdlib_path {
        let mut stdlib_path = PathBuf::from(stdlib_path);
        stdlib_path.push("src");
        stdlib_path.push("stdlib.tm");
        inputs.push(Input::try_from(stdlib_path)?);
    }

    match options.output_format {
        OutputFormat::Source => {
            for input in inputs.iter() {
                println!("{}", input.source());
            }

            Ok(())
        }
        OutputFormat::Ast => {
            let (inputs, ast) = parse(inputs);
            match ast
                .map_err(|d| d.with_inputs(inputs).to_string())
                .map(|ast| {
                    let mut out = String::new();
                    ast.ast_print(&AstPrintOptions::default(), &mut out)
                        .unwrap();
                    out
                }) {
                Ok(s) | Err(s) => {
                    println!("{s}");
                    Ok(())
                }
            }
        }
        OutputFormat::Hir => {
            let (inputs, ast) = parse(inputs);
            match ast
                .map(Nst::from)
                .and_then(Nst::resolve)
                .map_err(|d| d.with_inputs(inputs).to_string())
                .map(|hir| {
                    let mut out = String::new();
                    hir.hir_print(&HirPrintOptions::default(), &mut out)
                        .unwrap();
                    out
                }) {
                Ok(s) | Err(s) => {
                    println!("{s}");
                    Ok(())
                }
            }
        }
        _ => compile_inputs(inputs, dst, options),
    }
}

pub fn compile_inputs<D: AsRef<Path>>(
    src: Vec<Input>,
    dst: D,
    options: &Options,
) -> Result<(), String> {
    let mut ir_gen = LlvmIrGen::default();
    ir_gen.set_optimize(options.optimize);

    let (inputs, ast) = parse(src);
    ast.map(Nst::from)
        .and_then(Nst::resolve)
        .and_then(Mir::try_from)
        .and_then(|mir| ir_gen.gen(&mir))
        .and_then(|ir| produce_output(ir, dst.as_ref(), options))
        .map_err(|d| d.with_inputs(inputs).to_string())
}

fn produce_output(llvm_ir: LlvmIr, dst: &Path, options: &Options) -> Result<(), Diagnostics<()>> {
    match options.output_format {
        OutputFormat::Object => llvm_ir.build_bin(
            transmute_runtime::get_runtime(),
            dst,
            options.stdlib_path.as_deref(),
        ),
        OutputFormat::LlvmIr => {
            let dst = dst.with_extension("ll");
            llvm_ir.write_ir(&dst)
        }
        OutputFormat::Assembly => {
            let dst = dst.with_extension("s");
            llvm_ir.write_assembly(&dst)
        }
        OutputFormat::Source | OutputFormat::Ast | OutputFormat::Hir => {
            // already done
            Ok(())
        }
    }
}
