use std::fmt::{Debug, Formatter};
use transmute_core::ids::IdentRefId;
use transmute_core::span::Span;
use transmute_nst::nodes::Literal as NstLiteral;
use transmute_nst::nodes::LiteralKind as NstLiteralKind;

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

impl From<NstLiteral> for Literal {
    fn from(value: NstLiteral) -> Self {
        Self {
            span: value.span.clone(),
            kind: LiteralKind::from(value.kind),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(IdentRefId),
    Number(i64),
    String(String),
}

impl From<NstLiteralKind> for LiteralKind {
    fn from(value: NstLiteralKind) -> Self {
        match value {
            NstLiteralKind::Boolean(b) => Self::Boolean(b),
            NstLiteralKind::Identifier(i) => Self::Identifier(i),
            NstLiteralKind::Number(n) => Self::Number(n),
            NstLiteralKind::String(s) => Self::String(s),
        }
    }
}

impl Debug for LiteralKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            LiteralKind::Boolean(v) => write!(f, "Boolean({v})"),
            LiteralKind::Identifier(v) => write!(f, "IdentRefId({v})"),
            LiteralKind::Number(v) => write!(f, "Number({v})"),
            LiteralKind::String(v) => write!(f, "String({v})"),
        }
    }
}
