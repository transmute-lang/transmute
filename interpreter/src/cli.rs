use clap::Parser;

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    /// Script to execute
    pub script: String,

    /// Write Parsed AST file
    #[arg(long, default_value_t = false)]
    pub output_parsed: bool,

    /// Write HTML file
    #[arg(long, default_value_t = false)]
    pub output_html: bool,
}

pub fn parse_args() -> Cli {
    Cli::parse()
}
