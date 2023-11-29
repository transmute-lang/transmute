use crate::ast::ids::IdentRefId;
use crate::lexer::Span;

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

#[derive(Debug, Clone, PartialEq)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(IdentRefId),
    Number(i64),
}
