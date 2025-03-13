extern crate core;

use crate::cli::parse_args;
use std::{fs, process};
use tmi::exec;
use tmi::natives::InterpreterNatives;

mod cli;
// todo:check to check:
//  - let f() = 0:
//  - f = 1;

fn main() {
    let cli = parse_args();

    let script = match fs::read_to_string(&cli.script) {
        Ok(script) => script,
        Err(e) => {
            eprintln!("Could not read {}: {}", cli.script, e);
            process::exit(1);
        }
    };

    let mut params = cli.params;
    params.insert(0, "tmi".to_string());

    let context = InterpreterNatives::new(&params);

    exec(script, cli.output_parsed, context);
}
