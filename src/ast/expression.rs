use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
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

#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    Literal(Literal),
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    // todo vec does not hold span and position as it should
    MethodCall(Identifier, Vec<Expression>),
    Unary(UnaryOperator, Box<Expression>),
}
