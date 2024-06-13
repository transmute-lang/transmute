use crate::lexer::Span;
use std::fmt::{Display, Formatter};

#[derive(Debug, Clone, PartialEq)]
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

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
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

impl BinaryOperatorKind {
    pub fn precedence(&self) -> Precedence {
        match self {
            BinaryOperatorKind::Addition => Precedence::Sum,
            BinaryOperatorKind::Division => Precedence::Product,
            BinaryOperatorKind::Equality => Precedence::Comparison,
            BinaryOperatorKind::GreaterThan => Precedence::Comparison,
            BinaryOperatorKind::GreaterThanOrEqualTo => Precedence::Comparison,
            BinaryOperatorKind::Multiplication => Precedence::Product,
            BinaryOperatorKind::NonEquality => Precedence::Comparison,
            BinaryOperatorKind::SmallerThan => Precedence::Comparison,
            BinaryOperatorKind::SmallerThanOrEqualTo => Precedence::Comparison,
            BinaryOperatorKind::Subtraction => Precedence::Sum,
        }
    }

    pub fn function_name(&self) -> &'static str {
        match self {
            BinaryOperatorKind::Addition => "add",
            BinaryOperatorKind::Division => "div",
            BinaryOperatorKind::Equality => "eq",
            BinaryOperatorKind::GreaterThan => "gt",
            BinaryOperatorKind::GreaterThanOrEqualTo => "ge",
            BinaryOperatorKind::Multiplication => "mul",
            BinaryOperatorKind::NonEquality => "neq",
            BinaryOperatorKind::SmallerThan => "lt",
            BinaryOperatorKind::SmallerThanOrEqualTo => "le",
            BinaryOperatorKind::Subtraction => "sub",
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            BinaryOperatorKind::Addition => "+",
            BinaryOperatorKind::Division => "/",
            BinaryOperatorKind::Equality => "==",
            BinaryOperatorKind::GreaterThan => ">",
            BinaryOperatorKind::GreaterThanOrEqualTo => ">=",
            BinaryOperatorKind::Multiplication => "*",
            BinaryOperatorKind::NonEquality => "!=",
            BinaryOperatorKind::SmallerThan => "<",
            BinaryOperatorKind::SmallerThanOrEqualTo => "<=",
            BinaryOperatorKind::Subtraction => "-",
        }
    }
}

impl Display for BinaryOperatorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
// do not reorder!
pub enum Precedence {
    Lowest,
    Comparison,
    Sum,
    Product,
    Prefix,
    Access,
}

#[derive(Debug, Clone, PartialEq)]
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

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum UnaryOperatorKind {
    Minus,
}

impl UnaryOperatorKind {
    pub fn function_name(&self) -> &'static str {
        match self {
            UnaryOperatorKind::Minus => "neg",
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            UnaryOperatorKind::Minus => "-",
        }
    }
}

impl Display for UnaryOperatorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}
