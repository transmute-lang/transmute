#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::desugar::ImplicitRetConverter;
use crate::html::HtmlWriter;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::natives::Natives;
use crate::parser::Parser;
use crate::pretty_print::Options;
use crate::resolver::Resolver;
use std::fs::File;
use std::{fs, process};
use std::path::PathBuf;
use crate::cli:: parse_args;

mod ast;
mod desugar;
mod error;
mod exit_points;
mod html;
mod interpreter;
mod lexer;
mod natives;
mod parser;
mod pretty_print;
mod resolver;
mod vec_map;
mod xml;
mod cli;

// todo things to check:
//  let f() = 0:
//  f = 1;

// todo fix the ident().id() -> ident_id()

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

    exec(&script, cli.output_parsed, cli.output_executable, html_file_name);
}

fn exec(src: &str, print_ast: bool, print_executable_ast: bool, html_file_name: Option<PathBuf>) {
    let result = Parser::new(Lexer::new(src))
        .parse()
        .peek(|ast| {
            if print_ast {
                let mut w = String::new();
                let _ = ast.pretty_print(&Options::default(), &mut w);
                print!("Parsed AST:\n{w}\n");
            }
        })
        .map(|ast| ast.convert_implicit_ret(ImplicitRetConverter::new()))
        .and_then(|ast| ast.resolve(Resolver::new(), Natives::new()))
        .peek(|ast| {
            if print_executable_ast {
                let mut w = String::new();
                let _ = ast.pretty_print(&Options::default(), &mut w);
                print!("Executable AST:\n{w}\n");
            }
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
