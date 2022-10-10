use crate::lexer::Lexer;
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

    let lexer = Lexer::new(&file);
    for token in lexer {
        match token {
            Ok(token) => println!("{}", token),
            Err(e) => eprintln!("{}", e),
        }
    }
}
