use crate::ast::ids::IdentRefId;
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
