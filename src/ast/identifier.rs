use crate::lexer::Span;
use std::fmt::{Display, Formatter};

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

#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct IdentId {
    id: usize,
}

impl IdentId {
    pub fn id(&self) -> usize {
        self.id
    }
}

impl Display for IdentId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl From<usize> for IdentId {
    fn from(id: usize) -> Self {
        Self { id }
    }
}
