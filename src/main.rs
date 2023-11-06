extern crate core;

use crate::ast::PrettyPrint;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;

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
        println!("{}", PrettyPrint::new(&ast, *stmt));
    }

    let result = Interpreter::new(&ast).start();
    println!("Result: {}", result);
}
