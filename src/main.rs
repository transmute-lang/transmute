use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;

mod ast;
mod error;
mod interpreter;
mod lexer;
mod parser;

fn main() {
    let ast = Parser::new(Lexer::new("let forty = 2 * 20; forty + 2;"))
        .parse()
        .unwrap();
    let result = Interpreter::new(&ast).start();
    println!("Result: {}", result);
}
