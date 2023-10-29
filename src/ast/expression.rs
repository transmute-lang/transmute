use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::Visitor;
use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct Expression {
    kind: ExpressionKind,
    location: Location,
    span: Span,
}

impl Expression {
    pub fn new(kind: ExpressionKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn location(&self) -> &Location {
        &self.location
    }

    pub fn span(&self) -> &Span {
        &self.span
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
        let location = literal.location().clone();
        let span = literal.span().clone();
        Self::new(ExpressionKind::Literal(literal), location, span)
    }
}

#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    Literal(Literal),
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    MethodCall(Identifier, Vec<Expression>),
    Unary(UnaryOperator, Box<Expression>),
}
