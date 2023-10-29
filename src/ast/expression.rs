use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::Visitor;
use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct Expression {
    kind: ExpressionKind,
}

impl Expression {
    pub fn new(kind: ExpressionKind) -> Self {
        Self { kind }
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn location(&self) -> &Location {
        match &self.kind {
            ExpressionKind::Literal(l) => l.location(),
            ExpressionKind::Binary(e, _, _) => e.location(),
            ExpressionKind::Unary(o, _) => o.location(),
        }
    }

    pub fn span(&self) -> Span {
        match &self.kind {
            ExpressionKind::Literal(l) => l.span().clone(),
            ExpressionKind::Binary(l, _, r) => l.span().extend_to(&r.span()),
            ExpressionKind::Unary(o, e) => o.span().extend_to(&e.span()),
        }
    }

    pub fn accept<V, R>(&self, visitor: &mut V) -> R
    where
        V: Visitor<R>,
    {
        visitor.visit_expression(self)
    }
}

impl From<Literal> for Expression {
    fn from(literal: Literal) -> Self {
        Self {
            kind: ExpressionKind::Literal(literal),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    Literal(Literal),
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    Unary(UnaryOperator, Box<Expression>),
}
