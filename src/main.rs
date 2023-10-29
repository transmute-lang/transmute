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
    let mut interpreter = Interpreter::new();
    let result = ast.accept(&mut interpreter);
    println!("Result: {}", result);
}
