#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::ast::{Ast, AstNodePrettyPrint};
use crate::dot::Dot;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::natives::Natives;
use crate::parser::Parser;
use crate::symbol_table::SymbolTableGen;
use crate::type_check::TypeChecker;
use std::fs::File;

mod ast;
mod dot;
mod error;
mod exit_points;
mod interpreter;
mod lexer;
mod natives;
mod parser;
mod symbol_table;
mod type_check;
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
    let (ast, mut diagnostics) = Parser::new(Lexer::new(
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse();

    if !diagnostics.is_empty() {
        print!("Errors:\n{}", diagnostics);
        return;
    }

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    let (symbols, ast) = {
        let natives = Natives::default();
        let mut ast = ast.merge(Into::<Ast>::into(&natives));
        let (table, diagnostics) = SymbolTableGen::new(&mut ast, natives).build_table();
        if !diagnostics.is_empty() {
            print!("Errors:\n{}", diagnostics);
            return;
        }
        (table, ast)
    };

    Dot::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_rec_parsed_ast.dot").unwrap())
        .unwrap();

    let (ast, type_checker_diagnostics) = TypeChecker::new(ast, &symbols).check();
    diagnostics.append(type_checker_diagnostics);

    if diagnostics.is_empty() {
        print!(
            "Executable AST:\n{}",
            AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
        );
        Dot::new(&ast, &symbols)
            .write(&mut File::create("target/fibonacci_rec_executable_ast.dot").unwrap())
            .unwrap();
        let result = Interpreter::new(&ast, &symbols).start();
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

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );

    if !diagnostics.is_empty() {
        print!("Errors:\n{}", diagnostics);
        return;
    }

    let (symbols, ast) = {
        let natives = Natives::default();
        let mut ast = ast.merge(Into::<Ast>::into(&natives));
        let (table, diagnostics) = SymbolTableGen::new(&mut ast, natives).build_table();
        if !diagnostics.is_empty() {
            print!("Errors:\n{}", diagnostics);
            return;
        }
        (table, ast)
    };

    Dot::new(&ast, &symbols)
        .write(&mut File::create("target/fibonacci_iter_parsed_ast.dot").unwrap())
        .unwrap();

    let (ast, type_checker_diagnostics) = TypeChecker::new(ast, &symbols).check();
    diagnostics.append(type_checker_diagnostics);

    if diagnostics.is_empty() {
        print!(
            "Executable AST:\n{}",
            AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
        );
        Dot::new(&ast, &symbols)
            .write(&mut File::create("target/fibonacci_iter_executable_ast.dot").unwrap())
            .unwrap();
        let result = Interpreter::new(&ast, &symbols).start();
        println!("Result: {}", result);
    } else {
        print!("Errors:\n{}", diagnostics);
    }
}
