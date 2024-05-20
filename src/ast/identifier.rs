use crate::ast::ids::IdentId;
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    id: IdentId,
    span: Span,
}

impl Identifier {
    pub fn new(id: IdentId, span: Span) -> Self {
        Self { id, span }
    }

    pub fn id(&self) -> IdentId {
        self.id
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
