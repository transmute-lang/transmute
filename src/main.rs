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
use crate::xml::XmlWriter;
use std::fs::File;

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

// todo things to check:
//  let f() = 0:
//  f = 1;

// todo fix the ident().id() -> ident_id()

fn main() {
    exec(
        include_str!("../examples/fibonacci_rec.th"),
        "fibonacci_rec",
    );
    println!(
        "\n--------------------------------------------------------------------------------\n"
    );
    exec(
        include_str!("../examples/fibonacci_iter.th"),
        "fibonacci_iter",
    );
    println!(
        "\n--------------------------------------------------------------------------------\n"
    );
    exec(include_str!("../examples/area.th"), "area");

    // todo add example that returns a struct
}

fn exec(src: &str, name: &str) {
    let result = Parser::new(Lexer::new(src))
        .parse()
        .peek(|ast| {
            let mut w = String::new();
            let _ = ast.pretty_print(&Options::default(), &mut w);
            print!("Parsed AST:\n{w}\n");
        })
        .map(|ast| ast.convert_implicit_ret(ImplicitRetConverter::new()))
        .and_then(|ast| ast.resolve(Resolver::new(), Natives::new()))
        .peek(move |ast| {
            let mut w = String::new();
            let _ = ast.pretty_print(&Options::default(), &mut w);
            print!("Executable AST:\n{w}\n");
            XmlWriter::new(ast)
                .write(&mut File::create(format!("target/run__{name}.xml")).unwrap())
                .unwrap();
            HtmlWriter::new(ast)
                .write(&mut File::create(format!("target/html/run__{name}.html")).unwrap())
                .unwrap();
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
