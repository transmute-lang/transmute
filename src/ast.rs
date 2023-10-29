pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::Expression;
use crate::ast::literal::Literal;
use crate::ast::statement::Statement;
use crate::lexer::Span;

pub trait Visitor<R> {
    fn visit_statement(&mut self, stmt: &Statement) -> R;

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

    pub fn span(&self) -> Span {
        let start_span = self.root.first().unwrap().span();
        let stop_span = self.root.last().unwrap().span();
        start_span.extend_to(&stop_span)
    }

    pub fn accept<V, R>(&self, visitor: &mut V) -> R
    where
        V: Visitor<R>,
    {
        let mut ret: Option<R> = None;

        for statement in &self.root {
            ret = Some(visitor.visit_statement(statement))
        }

        ret.expect("ast has a value")
    }
}
