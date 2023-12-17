#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::ast::AstNodePrettyPrint;
use crate::dot::Dot;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::natives::Natives;
use crate::parser::Parser;
use crate::resolver::Resolver;
use crate::xml::XmlWriter;
use std::fs::File;

mod ast;
mod dot;
mod error;
mod exit_points;
mod interpreter;
mod lexer;
mod natives;
mod parser;
mod resolver;
mod xml;

// todo things to check:
//  let f() = 0:
//  f = 1;

fn main() {
    fibonacci_rec();
    println!();
    fibonacci_iter();
}

fn fibonacci_rec() {
    let (ast, diagnostics) = Parser::new(Lexer::new(
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse();

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    if !diagnostics.is_empty() {
        print!("Errors:\n{}", diagnostics);
        return;
    }

    let (ast, symbols) = Resolver::new(ast, Natives::default()).resolve().unwrap();

    Dot::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_rec.dot").unwrap())
        .unwrap();
    XmlWriter::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_rec.xml").unwrap())
        .unwrap();

    print!(
        "Executable AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    let result = Interpreter::new(&ast, &symbols).start();
    println!("Result: {}", result);
}

fn fibonacci_iter() {
    let (ast, diagnostics) = Parser::new(Lexer::new(
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
    ))
    .parse();

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    if !diagnostics.is_empty() {
        print!("Errors:\n{}", diagnostics);
        return;
    }

    let (ast, symbols) = Resolver::new(ast, Natives::default()).resolve().unwrap();

    Dot::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_iter.dot").unwrap())
        .unwrap();
    XmlWriter::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_iter.xml").unwrap())
        .unwrap();

    print!(
        "Executable AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    let result = Interpreter::new(&ast, &symbols).start();
    println!("Result: {}", result);
}
