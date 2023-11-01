pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::Expression;
use crate::ast::literal::Literal;
use crate::ast::statement::Statement;

pub trait Visitor<'a, R> {
    fn visit_ast(&mut self, ast: &'a Ast) -> R;

    fn visit_statement(&mut self, stmt: &'a Statement) -> R;

    fn visit_expression(&mut self, expr: &'a Expression) -> R;

    fn visit_literal(&mut self, literal: &'a Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast<'s> {
    root: Vec<Statement<'s>>,
}

impl<'s> Ast<'s> {
    pub fn new(root: Vec<Statement<'s>>) -> Self {
        assert!(!root.is_empty());
        Self { root }
    }

    pub fn statements(&self) -> &Vec<Statement<'s>> {
        &self.root
    }
}
