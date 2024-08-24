use crate::cli::parse_args;
use std::process;
use tmc::compile_file;

mod cli;

fn main() {
    let args = parse_args();

    println!(
        "Compiling {} to {}",
        args.input().display(),
        args.output().display()
    );

    match compile_file(&args.input(), &args.output()) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }
}
