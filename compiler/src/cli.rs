use clap::Parser;
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

    /// Outputs LLVM IR
    #[arg(long)]
    optimize: bool,

    /// Outputs LLVM IR
    #[arg(long, conflicts_with = "assembly")]
    llvm_ir: bool,

    /// Outputs Assembly
    #[arg(long, conflicts_with = "llvm_ir")]
    assembly: bool,
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
}
