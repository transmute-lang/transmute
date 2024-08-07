use transmute_core::ids::IdentId;
use transmute_core::span::Span;

/// Represents an identifier when not used as a reference
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

    pub fn take_span(self) -> Span {
        self.span
    }
}
