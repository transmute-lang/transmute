use crate::cli::parse_args;
use std::process;
use tmc::{compile_nst, Options, OutputFormat};
use transmute_nst::builder::{Block, FnCall, Function, If, Namespace, NstBuilder, Ret, ToIdentId};
use transmute_nst::nodes::Nst;

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

    #[cfg(feature = "static-nst")]
    match compile_nst(nst(), &args.output(), &options) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }

    #[cfg(not(feature = "static-nst"))]
    match compile_file(&args.input(), &args.output(), &options) {
        Ok(_) => {}
        Err(e) => {
            eprintln!("{e}");
            process::exit(1)
        }
    }
}

#[cfg(feature = "static-nst")]
fn nst() -> Nst {
    let mut builder = NstBuilder::new();

    let mut root_ns = Namespace::new("<root>");
    let mut core_ns = Namespace::new("core");
    root_ns.push(core_ns);

    let number = builder.push_type_def("number");

    let mut fibonacci = Function::new("fibonacci");
    let n = "n".to_ident_id(&mut builder);
    fibonacci.add_parameter(n, number);
    fibonacci.with_ret_type(number);

    let mut block = Block::new();

    let mut ret_block = Block::new();
    ret_block.push(Ret::new(n));

    block.push(If::new(
        FnCall::new("lt".to_ident_id(&mut builder))
            .with_parameter(n)
            .with_parameter(2),
        ret_block,
    ));

    block.push(
        FnCall::new("add".to_ident_id(&mut builder))
            .with_parameter(
                FnCall::new("fibonacci".to_ident_id(&mut builder)).with_parameter(
                    FnCall::new("sub".to_ident_id(&mut builder))
                        .with_parameter(n)
                        .with_parameter(1),
                ),
            )
            .with_parameter(
                FnCall::new("fibonacci".to_ident_id(&mut builder)).with_parameter(
                    FnCall::new("sub".to_ident_id(&mut builder))
                        .with_parameter(n)
                        .with_parameter(2),
                ),
            ),
    );

    fibonacci.with_body(block);
    root_ns.push(fibonacci);

    let mut main = Function::new("main");
    let mut block = Block::new();
    block.push(
        FnCall::new("print".to_ident_id(&mut builder))
            .with_parameter(FnCall::new("fibonacci".to_ident_id(&mut builder)).with_parameter(10)),
    );
    main.with_body(block);

    root_ns.push(main);

    let stmt_id = builder.append_statement(root_ns);
    builder.set_root(stmt_id);
    Into::<Nst>::into(builder)
}
