use crate::cli::parse_args;
use std::process;
use tmc::{compile_file, Options, OutputFormat};

mod cli;

fn main() {
    let args = parse_args();

    println!(
        "Compiling {} to {}",
        args.input().display(),
        args.output().display()
    );

    let mut options = Options::default();
    if args.output_llvm_ir() {
        options.set_output_format(OutputFormat::LlvmIr);
    } else if args.output_assembly() {
        options.set_output_format(OutputFormat::Assembly);
    } else if args.output_source() {
        options.set_output_format(OutputFormat::Source);
    }
    options.set_optimize(args.optimize());
    if let Some(stdlib_path) = args.stdlib_path() {
        options.set_stdlib_path(stdlib_path);
    }

    match compile_file(&args.input(), &args.output(), &options) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }
}
