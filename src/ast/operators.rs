use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct BinaryOperator {
    kind: BinaryOperatorKind,
    span: Span,
}

impl BinaryOperator {
    pub fn new(kind: BinaryOperatorKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &BinaryOperatorKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum BinaryOperatorKind {
    Addition,
    Division,
    Multiplication,
    Subtraction,
}

#[derive(Debug, PartialEq)]
pub struct UnaryOperator {
    kind: UnaryOperatorKind,
    span: Span,
}

impl UnaryOperator {
    pub fn new(kind: UnaryOperatorKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &UnaryOperatorKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum UnaryOperatorKind {
    Minus,
}
