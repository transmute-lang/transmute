use std::fmt::{Debug, Formatter};
use transmute_core::ids::IdentRefId;
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
}

impl Literal {
    pub fn new(kind: LiteralKind, span: Span) -> Self {
        Self { kind, span }
    }
}

#[derive(Clone, PartialEq)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(IdentRefId),
    Number(i64),
}

impl Debug for LiteralKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralKind::Boolean(v) => write!(f, "Boolean({v})"),
            LiteralKind::Identifier(v) => write!(f, "IdentRefId({v})"),
            LiteralKind::Number(v) => write!(f, "Number({v})"),
        }
    }
}
