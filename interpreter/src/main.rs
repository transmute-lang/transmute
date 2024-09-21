extern crate core;

use crate::cli::parse_args;
use std::path::PathBuf;
use std::{fs, process};
use tmi::exec;

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

    let html_file_name = if cli.output_html {
        let path = PathBuf::from(&cli.script);

        let mut file_name = path.file_name().expect("we could read it").to_os_string();
        file_name.push(".html");

        let mut path = PathBuf::from("target");
        path.push(file_name);

        Some(path)
    } else {
        None
    };

    exec(&script, cli.output_parsed, html_file_name, cli.params);
}
