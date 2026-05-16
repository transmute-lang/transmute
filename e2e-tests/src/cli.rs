use crate::Kind;
use clap::{Parser, ValueEnum};
use std::collections::HashSet;

#[derive(Debug)]
pub struct CliConfig {
    pub kinds: HashSet<Kind>,
    pub verbose: bool,
    pub no_gc: bool,
}

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    /// The scopes
    #[arg(short, long, value_enum, default_values_t = Scope::value_variants().to_vec())]
    scopes: Vec<Scope>,
    /// Verbose output (print compiler's output)
    #[arg(long)]
    verbose: bool,
    /// Disable GC
    #[arg(long)]
    no_gc: bool,
}

impl From<Args> for CliConfig {
    fn from(value: Args) -> Self {
        CliConfig {
            kinds: value
                .scopes
                .into_iter()
                .map(|s| s.into())
                .collect::<HashSet<_>>(),
            verbose: value.verbose,
            no_gc: value.no_gc,
        }
    }
}

#[derive(ValueEnum, Clone)]
enum Scope {
    Llvm,
    C,
}

impl From<Scope> for Kind {
    fn from(value: Scope) -> Self {
        match value {
            Scope::Llvm => Kind::Llvm,
            Scope::C => Kind::C,
        }
    }
}

pub fn parse_args() -> CliConfig {
    Args::parse().into()
}
