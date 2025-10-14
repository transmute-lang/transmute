use crate::cli::parse_args;
use std::fmt::format;
use std::os::unix::prelude::CommandExt;
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
    } else if args.output_ast() {
        options.set_output_format(OutputFormat::Ast);
    } else if args.output_hir() {
        options.set_output_format(OutputFormat::Hir);
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

    if args.run() {
        eprintln!(
            "running {}\n{dashes}",
            args.output().display(),
            dashes = "-".repeat(8 + args.output().display().to_string().len())
        );
        // https://users.rust-lang.org/t/is-there-a-windows-eauivalent-of-std-exec/70262
        // https://docs.rs/cargo-util/0.1.1/cargo_util/struct.ProcessBuilder.html#method.exec_replace
        process::Command::new(format!("./{}", &args.output().display())).exec();
    }
}
