use crate::lexer::Span;
use std::fmt::{Display, Formatter};

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
    Equality,
    GreaterThan,
    GreaterThanOrEqualTo,
    Multiplication,
    NonEquality,
    SmallerThan,
    SmallerThanOrEqualTo,
    Subtraction,
}

impl Display for BinaryOperatorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            BinaryOperatorKind::Addition => write!(f, "+"),
            BinaryOperatorKind::Division => write!(f, "/"),
            BinaryOperatorKind::Equality => write!(f, "=="),
            BinaryOperatorKind::GreaterThan => write!(f, ">"),
            BinaryOperatorKind::GreaterThanOrEqualTo => write!(f, ">="),
            BinaryOperatorKind::Multiplication => write!(f, "*"),
            BinaryOperatorKind::NonEquality => write!(f, "!="),
            BinaryOperatorKind::SmallerThan => write!(f, "<"),
            BinaryOperatorKind::SmallerThanOrEqualTo => write!(f, "<="),
            BinaryOperatorKind::Subtraction => write!(f, "-"),
        }
    }
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

impl Display for UnaryOperatorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            UnaryOperatorKind::Minus => write!(f, "-"),
        }
    }
}
