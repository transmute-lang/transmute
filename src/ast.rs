pub mod expression;
pub mod literal;
pub mod operators;

use crate::ast::expression::Expression;
use crate::ast::literal::Literal;
use crate::lexer::Span;

pub trait Visitor<R> {
    fn visit_ast(&mut self, ast: &Ast) -> R;

    fn visit_expression(&mut self, expr: &Expression) -> R;

    fn visit_literal(&mut self, literal: &Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    root: Expression,
}

impl Ast {
    pub fn new(root: Expression) -> Self {
        Self { root }
    }

    pub fn span(&self) -> Span {
        self.root.span()
    }

    pub fn expression(&self) -> &Expression {
        &self.root
    }

    pub fn accept<V, R>(&self, visitor: &mut V) -> R
    where
        V: Visitor<R>,
    {
        visitor.visit_ast(self)
    }
}
