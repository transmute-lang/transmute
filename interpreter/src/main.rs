#![allow(dead_code)] // todo:refactoring eventually remove
extern crate core;

use crate::cli::parse_args;
use crate::interpreter::Interpreter;
use std::fs::File;
use std::path::PathBuf;
use std::{fs, process};
use transmute_ast::lexer::Lexer;
use transmute_ast::parser::Parser;
use transmute_ast::pretty_print::Options;
use transmute_hir::natives::Natives;
use transmute_hir::output::html::HtmlWriter;
use transmute_hir::UnresolvedHir;

mod cli;
mod interpreter;
pub mod value;

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

    exec(&script, cli.output_parsed, html_file_name);
}
fn exec(src: &str, print_ast: bool, html_file_name: Option<PathBuf>) {
    let result = Parser::new(Lexer::new(src))
        .parse()
        .peek(|ast| {
            if print_ast {
                let mut w = String::new();
                let _ = ast.pretty_print(&Options::default(), &mut w);
                print!("Parsed AST:\n{w}\n");
            }
        })
        .map(UnresolvedHir::from)
        .and_then(|hir| hir.resolve(Natives::new()))
        .peek(|ast| {
            if let Some(html_file_name) = &html_file_name {
                HtmlWriter::new(ast)
                    .write(&mut File::create(html_file_name).unwrap())
                    .unwrap();
            }
        })
        .map(|ast| Interpreter::new(&ast).start());

    match result {
        Ok(res) => {
            println!("Result: {}", res)
        }
        Err(err) => {
            print!("Errors:\n{}", err)
        }
    }
}

trait Peek<T, E> {
    fn peek<F: for<'a> Fn(&'a T)>(self, f: F) -> Result<T, E>;
}

impl<T, E> Peek<T, E> for Result<T, E> {
    fn peek<F: for<'a> Fn(&'a T)>(self, f: F) -> Result<T, E> {
        if let Ok(v) = &self {
            f(v)
        }
        self
    }
}
