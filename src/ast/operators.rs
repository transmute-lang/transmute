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
    Multiplication,
    Subtraction,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOperator {
    kind: UnaryOperatorKind,
    location: Location,
    span: Span,
}

impl UnaryOperator {
    pub fn new(kind: UnaryOperatorKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }

    pub fn kind(&self) -> &UnaryOperatorKind {
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
pub enum UnaryOperatorKind {
    Minus,
}
