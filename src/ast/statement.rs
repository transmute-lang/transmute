use crate::ast::expression::Expression;
use crate::ast::identifier::Identifier;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct Statement {
    kind: StatementKind,
    span: Span,
}

impl Statement {
    pub fn new(kind: StatementKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &StatementKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum StatementKind {
    Expression(Expression),
    Let(Identifier, Expression),
    Ret(Expression),
    // todo vec does not hold span and position as it should
    LetFn(Identifier, Vec<Identifier>, Vec<Statement>),
}
