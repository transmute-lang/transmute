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
    root: Vec<TopLevel>,
}

impl Ast {
    pub fn new(root: Vec<TopLevel>) -> Self {
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

        for top_level in &self.root {
            ret = Some(match top_level {
                TopLevel::Expression(e) => visitor.visit_expression(e),
                TopLevel::Statement(s) => visitor.visit_statement(s),
            })
        }

        ret.expect("ast has a value")
    }
}

#[derive(Debug, PartialEq)]
pub enum TopLevel {
    Expression(Expression),
    Statement(Statement),
}

impl TopLevel {
    pub fn span(&self) -> Span {
        match self {
            TopLevel::Expression(e) => e.span(),
            TopLevel::Statement(s) => s.span().clone(),
        }
    }
}
