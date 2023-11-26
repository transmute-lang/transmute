#![allow(dead_code)] // fixme eventually remove
extern crate core;

use crate::ast::AstNodePrettyPrint;
use crate::interpreter::Interpreter;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::predefined::Predefined;
use crate::resolver::Resolver;
use crate::symbol_table::SymbolTableGen;
use crate::type_check::TypeChecker;

mod ast;
mod error;
mod exit_points;
mod interpreter;
mod lexer;
mod parser;
mod predefined;
mod resolver;
mod symbol_table;
mod type_check;
mod xml;

fn main() {
    let (ast, mut diagnostics) = Parser::new(Lexer::new(
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
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
        AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
    );
    let type_checker_diagnostics = TypeChecker::new(&ast, &symbols, &Predefined::new()).check();
    diagnostics.append(type_checker_diagnostics);

    if diagnostics.is_empty() {
        let result = Interpreter::new(&ast).start();
        println!("Result: {}", result);
    } else {
        print!("Errors:\n{}", diagnostics);
    }
}
