#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::resolver::Resolver;
use crate::symbol_table::SymbolTableGen;

mod ast;
mod error;
mod interpreter;
mod lexer;
mod parser;
mod resolver;
mod symbol_table;

fn main() {
    let ast = Parser::new(Lexer::new(
        "let f(n) = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse()
    .expect("source is valid");

    let (symbols, ast) = {
        let mut ast = ast;
        (SymbolTableGen::new(&mut ast).build_table(), ast)
    };

    let ast = Resolver::new(ast, &symbols)
        .resolve_symbols()
        .expect("source is valid");

    let result = Interpreter::new(&ast).start();
    println!("Result: {}", result);
}
