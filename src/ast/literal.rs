use crate::ast::identifier::Identifier;
use crate::ast::Visitor;
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

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn accept<'a, V, R>(&self, visitor: &mut V) -> R
    where
        V: Visitor<'a, R>,
    {
        visitor.visit_literal(self)
    }
}

#[derive(Debug, PartialEq)]
pub enum LiteralKind {
    Identifier(Identifier),
    Number(i64),
}
