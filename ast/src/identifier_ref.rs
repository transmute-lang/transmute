use crate::identifier::Identifier;
use std::fmt::Debug;
use transmute_core::ids::{IdentId, IdentRefId};
use transmute_core::span::Span;

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef {
    /// ID of this identifier reference
    id: IdentRefId,
    /// The referenced symbol identifier
    ident: Identifier,
}

impl IdentifierRef {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self { id, ident }
    }

    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier {
        &self.ident
    }

    pub fn take_ident(self) -> Identifier {
        self.ident
    }

    pub fn ident_id(&self) -> IdentId {
        self.ident.id()
    }

    pub fn span(&self) -> &Span {
        self.ident.span()
    }
}
