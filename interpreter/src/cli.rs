use clap::Parser;

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    /// Script to execute
    pub script: String,

    /// Write Parsed AST file
    #[arg(long, default_value_t = false)]
    pub output_parsed: bool,

    /// The parameters to pass to main
    pub params: Vec<String>,
}

pub fn parse_args() -> Cli {
    Cli::parse()
}
