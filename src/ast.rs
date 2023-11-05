pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{ExprId, Expression};
use crate::ast::identifier::IdentId;
use crate::ast::literal::Literal;
use crate::ast::statement::{Statement, StmtId};

pub trait Visitor<R> {
    fn visit_ast(&mut self, ast: &Ast) -> R;

    fn visit_statement(&mut self, stmt: StmtId) -> R;

    fn visit_expression(&mut self, expr: ExprId) -> R;

    fn visit_literal(&mut self, literal: &Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    identifiers: Vec<String>,
    expressions: Vec<Expression>,
    statements: Vec<Statement>,
    // todo replace with Statements
    root: Vec<StmtId>,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        expressions: Vec<Expression>,
        statements: Vec<Statement>,
        root: Vec<StmtId>,
    ) -> Self {
        assert!(!root.is_empty());
        Self {
            identifiers,
            expressions,
            statements,
            root,
        }
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifier(&self, id: &IdentId) -> &String {
        &self.identifiers[id.id()]
    }

    pub fn expression(&self, id: &ExprId) -> &Expression {
        &self.expressions[id.id()]
    }

    pub fn statement(&self, id: &StmtId) -> &Statement {
        &self.statements[id.id()]
    }
}
