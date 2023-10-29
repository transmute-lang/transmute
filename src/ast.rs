pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::Expression;
use crate::ast::literal::Literal;
use crate::ast::statement::Statement;

pub trait Visitor<'a, R> {
    fn visit_statement(&mut self, stmt: &'a Statement) -> R;

    fn visit_expression(&mut self, expr: &Expression) -> R;

    fn visit_literal(&mut self, literal: &Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    root: Vec<Statement>,
}

impl Ast {
    pub fn new(root: Vec<Statement>) -> Self {
        assert!(!root.is_empty());
        Self { root }
    }

    pub fn accept<'a, V, R>(&'a self, visitor: &mut V) -> R
    where
        V: Visitor<'a, R>,
    {
        let mut ret: Option<R> = None;

        for statement in &self.root {
            ret = Some(visitor.visit_statement(statement))
        }

        ret.expect("ast has a value")
    }
}
