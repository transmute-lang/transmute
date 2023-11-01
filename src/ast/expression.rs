use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::Statement;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct Expression {
    kind: ExpressionKind,
    span: Span,
}

impl Expression {
    pub fn new(kind: ExpressionKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        let span = literal.span().clone();
        Self::new(ExpressionKind::Literal(literal), span)
    }
}

// todo vec does not hold span and position as it should
#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    Assignment(Identifier, Box<Expression>),
    If(Box<Expression>, Vec<Statement>, Option<Vec<Statement>>),
    Literal(Literal),
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    FunctionCall(Identifier, Vec<Expression>),
    Unary(UnaryOperator, Box<Expression>),
    While(Box<Expression>, Vec<Statement>),
}
