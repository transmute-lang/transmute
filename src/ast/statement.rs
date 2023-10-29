use crate::ast::expression::Expression;
use crate::ast::identifier::Identifier;
use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct Statement {
    kind: StatementKind,
    location: Location,
    span: Span,
}

impl Statement {
    pub fn new(kind: StatementKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }

    pub fn kind(&self) -> &StatementKind {
        &self.kind
    }

    pub fn location(&self) -> &Location {
        &self.location
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, PartialEq)]
pub enum StatementKind {
    Expression(Expression),
    Let(Identifier, Expression),
    LetFn(Identifier, Vec<Identifier>, Expression),
}
