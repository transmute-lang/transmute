use crate::cli::parse_args;
use std::{fs, process};
use transmute_ast::parse;
use transmute_hir::resolve;
use transmute_llvm::LlvmIrGen;

mod cli;

fn main() {
    let args = parse_args();

    let file_content = match fs::read_to_string(args.input()) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Could not read {}: {}", args.input().display(), e);
            process::exit(1);
        }
    };

    println!(
        "Compiling {} to {}",
        args.input().display(),
        args.output().display()
    );

    let ir_gen = LlvmIrGen::default();
    let ir = parse(&file_content)
        .and_then(resolve)
        .and_then(|hir| ir_gen.gen(&hir));

    let ir = match ir {
        Ok(ir) => ir,
        Err(diagnostics) => {
            eprintln!("{diagnostics}");
            process::exit(1)
        }
    };

    ir.build_bin(transmute_crt::get_crt(), args.output())
        .unwrap();
}
