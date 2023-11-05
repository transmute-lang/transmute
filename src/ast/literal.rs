use crate::ast::identifier::Identifier;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
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
}

#[derive(Debug, PartialEq)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(Identifier),
    Number(i64),
}
