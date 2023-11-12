#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::ast::AstNodePrettyPrint;
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
    let (ast, mut diagnostics) = Parser::new(Lexer::new(
        "let f(n) = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
    ))
    .parse();

    let (symbols, ast) = {
        let mut ast = ast;
        (SymbolTableGen::new(&mut ast).build_table(), ast)
    };

    let (ast, resolver_diagnostics) = Resolver::new(ast, &symbols).resolve_symbols();
    diagnostics.append(resolver_diagnostics);

    print!(
        "Parsed AST:\n{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().last().unwrap())
    );
    println!();
    print!("Errors:\n{}", diagnostics);

    if diagnostics.is_empty() {
        let result = Interpreter::new(&ast).start();
        println!("Result: {}", result);
    }

    // second

    let (ast, diagnostics) = Parser::new(Lexer::new(
        "let f ( n ) = { if n <=  { ret n ; } f ( n - 1 ) + f ( n - 2 ) ; } f ( 9 ) + 8 ;",
    ))
    .parse();

    print!(
        "Parsed AST:\n{}{}",
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap()),
        AstNodePrettyPrint::new(&ast, *ast.statements().last().unwrap())
    );
    println!();
    print!("Errors:\n{}", diagnostics);
}
