use crate::ast::ids::IdentId;
use crate::lexer::Span;

/// Represents an identifier when not used a reference
// todo add ref to symbol Id
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
