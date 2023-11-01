use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::Statement;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct Expression<'s> {
    kind: ExpressionKind<'s>,
    span: Span,
}

impl<'s> Expression<'s> {
    pub fn new(kind: ExpressionKind<'s>, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &ExpressionKind<'s> {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl<'s> From<Literal<'s>> for Expression<'s> {
    fn from(literal: Literal<'s>) -> Self {
        let span = literal.span().clone();
        Self::new(ExpressionKind::Literal(literal), span)
    }
}

// todo vec does not hold span and position as it should
#[derive(Debug, PartialEq)]
pub enum ExpressionKind<'s> {
    Assignment(Identifier<'s>, Box<Expression<'s>>),
    If(
        Box<Expression<'s>>,
        Vec<Statement<'s>>,
        Option<Vec<Statement<'s>>>,
    ),
    Literal(Literal<'s>),
    Binary(Box<Expression<'s>>, BinaryOperator, Box<Expression<'s>>),
    FunctionCall(Identifier<'s>, Vec<Expression<'s>>),
    Unary(UnaryOperator, Box<Expression<'s>>),
    While(Box<Expression<'s>>, Vec<Statement<'s>>),
}
