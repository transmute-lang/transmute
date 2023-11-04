use crate::ast::identifier::Identifier;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct Literal<'s> {
    kind: LiteralKind<'s>,
    span: Span,
}

impl<'s> Literal<'s> {
    pub fn new(kind: LiteralKind<'s>, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &LiteralKind<'s> {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum LiteralKind<'s> {
    Boolean(bool),
    Identifier(Identifier<'s>),
    Number(i64),
}
