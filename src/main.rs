use crate::lexer::Lexer;
use std::{env, fs};

mod lexer;

fn main() {
    let args: Vec<String> = env::args().collect();

    let file = fs::read_to_string(&args[1]).unwrap();

    let mut lexer = Lexer::new(&file);
    for token in lexer {
        match token {
            Ok(token) => println!("{}", token),
            Err(e) => eprintln!("{}", e),
        }
    }
}
