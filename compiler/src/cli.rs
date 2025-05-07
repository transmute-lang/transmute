use clap::Parser;
use std::env;
use std::path::PathBuf;

pub fn parse_args() -> Args {
    Args::parse()
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    /// Input files
    input: String,

    /// Output file
    #[arg(short, long)]
    output: Option<String>,

    /// Optimize
    #[arg(long)]
    optimize: bool,

    /// Outputs LLVM IR
    #[arg(long, conflicts_with_all = ["assembly", "source", "ast"])]
    llvm_ir: bool,

    /// Outputs Assembly
    #[arg(long, conflicts_with_all = ["llvm_ir", "source", "ast"])]
    assembly: bool,

    /// Outputs Source
    #[arg(long, conflicts_with_all = ["llvm_ir", "assembly", "ast"])]
    source: bool,

    /// Outputs Ast
    #[arg(long, conflicts_with_all = ["assembly", "llvm_ir", "source"])]
    ast: bool,

    /// Path to the stdlib library. If not provided, use `TRANSMUTE_STDLIB_PATH` env. variable if set.
    #[arg(long)]
    stdlib_path: Option<String>,
}

impl Args {
    pub fn input(&self) -> PathBuf {
        PathBuf::from(&self.input)
    }

    pub fn output(&self) -> PathBuf {
        self.output.as_ref().map(PathBuf::from).unwrap_or_else(|| {
            let input = self.input();
            let filename = input.file_name().unwrap().to_str().unwrap();
            let filename = &filename[0..filename.len() - 3];
            input.parent().unwrap().with_file_name(filename)
        })
    }

    pub fn optimize(&self) -> bool {
        self.optimize
    }

    pub fn output_llvm_ir(&self) -> bool {
        self.llvm_ir
    }

    pub fn output_assembly(&self) -> bool {
        self.assembly
    }

    pub fn output_source(&self) -> bool {
        self.source
    }

    pub fn output_ast(&self) -> bool {
        self.ast
    }

    pub fn stdlib_path(&self) -> Option<PathBuf> {
        self.stdlib_path
            .as_ref()
            .map(PathBuf::from)
            .or_else(|| env::var("TRANSMUTE_STDLIB_PATH").ok().map(PathBuf::from))
    }
}
