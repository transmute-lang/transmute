use crate::lexer::Lexer;
use crate::parser::Parser;
use std::{env, fs};

#[allow(dead_code)]
mod lexer;
#[allow(dead_code)]
mod parser;
#[allow(dead_code)]
mod utils;

fn main() {
    let args: Vec<String> = env::args().collect();

    let file = fs::read_to_string(&args[1]).unwrap();

    let parser = Parser::new(Lexer::new(&file));
    match parser.parse() {
        Ok(root) => println!("{:?}", root),
        Err(errors) => {
            for error in errors {
                println!("{}", error);
            }
        }
    }
}
