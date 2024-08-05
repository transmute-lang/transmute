use crate::ast::literal::Literal as AstLiteral;
use crate::ast::literal::LiteralKind as AstLiteralKind;
use crate::ids::IdentRefId;
use crate::lexer::Span;
use std::fmt::{Debug, Formatter};

#[derive(Debug, Clone, PartialEq)]
pub struct Literal {
    kind: LiteralKind,
    span: Span,
}

impl Literal {
    pub fn new(kind: LiteralKind, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &LiteralKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl From<AstLiteral> for Literal {
    fn from(value: AstLiteral) -> Self {
        Self {
            span: value.span().clone(),
            kind: LiteralKind::from(value.take_kind()),
        }
    }
}

#[derive(Clone, PartialEq)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(IdentRefId),
    Number(i64),
}

impl From<AstLiteralKind> for LiteralKind {
    fn from(value: AstLiteralKind) -> Self {
        match value {
            AstLiteralKind::Boolean(b) => Self::Boolean(b),
            AstLiteralKind::Identifier(i) => Self::Identifier(i),
            AstLiteralKind::Number(n) => Self::Number(n),
        }
    }
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
