use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct BinaryOperator {
    kind: BinaryOperatorKind,
    location: Location,
    span: Span,
}

impl BinaryOperator {
    pub fn new(kind: BinaryOperatorKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }

    pub fn kind(&self) -> &BinaryOperatorKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum BinaryOperatorKind {
    Addition,
}
