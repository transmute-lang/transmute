extern crate core;

use crate::ast::AstNodePrettyPrint;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::symbol_table::{ScopeId, ScopePrettyPrint, SymbolTableGen};

mod ast;
mod error;
mod interpreter;
mod lexer;
mod parser;
mod symbol_table;

fn main() {
    let ast = Parser::new(Lexer::new(
        "let f(n) = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse()
    .expect("source is valid");

    for stmt in ast.statements() {
        println!("{}", AstNodePrettyPrint::new(&ast, *stmt));
    }

    let (symbols, ast) = {
        let mut ast = ast;
        (SymbolTableGen::new(&mut ast).build_table(), ast)
    };

    println!(
        "{}",
        ScopePrettyPrint::new(&symbols, &ast, ScopeId::from(2))
    );

    let result = Interpreter::new(&ast).start();
    println!("Result: {}", result);
}
