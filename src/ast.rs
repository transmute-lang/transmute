pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{ExprId, Expression};
use crate::ast::literal::Literal;
use crate::ast::statement::{Statement, StmtId};

pub trait Visitor<'a, R> {
    fn visit_ast(&mut self, ast: &'a Ast) -> R;

    fn visit_statement(&mut self, stmt: &'a Statement) -> R;

    fn visit_expression(&mut self, expr: &'a Expression) -> R;

    fn visit_literal(&mut self, literal: &'a Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast<'s> {
    expressions: Vec<Expression<'s>>,
    statements: Vec<Statement<'s>>,
    // todo replace with Statements
    root: Vec<StmtId>,
}

impl<'s> Ast<'s> {
    pub fn new(
        expressions: Vec<Expression<'s>>,
        statements: Vec<Statement<'s>>,
        root: Vec<StmtId>,
    ) -> Self {
        assert!(!root.is_empty());
        Self {
            expressions,
            statements,
            root,
        }
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn expression(&self, id: &ExprId) -> &Expression<'s> {
        &self.expressions[id.id()]
    }

    pub fn statement(&self, id: &StmtId) -> &Statement<'s> {
        &self.statements[id.id()]
    }
}
