use crate::ast::identifier::Identifier;
use crate::ast::Visitor;
use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct Literal {
    kind: LiteralKind,
    location: Location,
    span: Span,
}

impl Literal {
    pub fn new(kind: LiteralKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }

    pub fn kind(&self) -> &LiteralKind {
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
        visitor.visit_literal(self)
    }
}

#[derive(Debug, PartialEq)]
pub enum LiteralKind {
    Identifier(Identifier),
    Number(i64),
}
