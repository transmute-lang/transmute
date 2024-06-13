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
    fibonacci_rec();
    println!(
        "\n--------------------------------------------------------------------------------\n"
    );
    fibonacci_iter();
    println!(
        "\n--------------------------------------------------------------------------------\n"
    );
    points();
}

fn fibonacci_rec() {
    exec(
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
        "fibonacci_rec",
    );
}

fn fibonacci_iter() {
    exec(
        r#"
            let f(n: number): number = {
                if n == 0 { ret 0; }
                if n == 1 { ret 1; }

                let prev_prev = 0;
                let prev = 1;
                let current = 0;

                while n > 1 {
                    current = prev_prev + prev;
                    prev_prev = prev;
                    prev = current;
                    n = n - 1;
                }

                current;
            }
            f(9) + 8;
        "#,
        "fibonacci_iter",
    );
}

fn points() {
    // todo return Point
    exec(
        r#"
            struct Point {
                x: number,
                y: number
            }

            let area(p1: Point, p2: Point): number = {
                (p2.x - p1.x) * (p2.y - p1.y);
            }

            area(
                Point {
                    x: 1,
                    y: 1
                },
                Point {
                    x: 1 + 6,
                    y: 1 + 7
                }
            );
        "#,
        "points",
    )
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
