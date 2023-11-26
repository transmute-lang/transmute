#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::ast::AstNodePrettyPrint;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::predefined::Predefined;
use crate::symbol_table::SymbolTableGen;
use crate::type_check::TypeChecker;

mod ast;
mod error;
mod exit_points;
mod interpreter;
mod lexer;
mod parser;
mod predefined;
mod symbol_table;
mod type_check;
mod xml;

fn main() {
    fibonacci_rec();
    println!();
    fibonacci_iter();
}

fn fibonacci_rec() {
    let (ast, mut diagnostics) = Parser::new(Lexer::new(
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse();

    let (symbols, ast) = {
        let mut ast = ast;
        (SymbolTableGen::new(&mut ast).build_table(), ast)
    };

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );
    let (ast, type_checker_diagnostics) =
        TypeChecker::new(ast, &symbols, &Predefined::new()).check();
    diagnostics.append(type_checker_diagnostics);

    if diagnostics.is_empty() {
        let result = Interpreter::new(&ast).start();
        println!("Result: {}", result);
    } else {
        print!("Errors:\n{}", diagnostics);
    }
}

fn fibonacci_iter() {
    let (ast, mut diagnostics) = Parser::new(Lexer::new(
        r#"
            let f(n: number): number = {
                if n == 0 { ret 0; }
                if n == 1 { ret 1; }

                let prev_prev = 0;
                let prev = 1;
                let current = 0;

                let m = n;
                while m > 1 {
                    current = prev_prev + prev;
                    prev_prev = prev;
                    prev = current;
                    m = m - 1;
                }

                current;
            }
            f(9) + 8;
        "#,
    ))
    .parse();

    let (symbols, ast) = {
        let mut ast = ast;
        (SymbolTableGen::new(&mut ast).build_table(), ast)
    };

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );
    let (ast, type_checker_diagnostics) =
        TypeChecker::new(ast, &symbols, &Predefined::new()).check();
    diagnostics.append(type_checker_diagnostics);

    if diagnostics.is_empty() {
        let result = Interpreter::new(&ast).start();
        println!("Result: {}", result);
    } else {
        print!("Errors:\n{}", diagnostics);
    }
}
