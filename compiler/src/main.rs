use crate::cli::parse_args;
use std::process;
use tmc::{compile_file, Options};

mod cli;

fn main() {
    let args = parse_args();

    println!(
        "Compiling {} to {}",
        args.input().display(),
        args.output().display()
    );

    let mut options = Options::default();
    options.set_llvm_ir(args.output_llvm_ir());
    options.set_optimize(args.optimize());

    match compile_file(&args.input(), &args.output(), &options) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }
}
