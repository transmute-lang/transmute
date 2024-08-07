use crate::identifier::Identifier;
use std::fmt::Debug;
use transmute_core::ids::IdentRefId;

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef {
    /// ID of this identifier reference
    pub id: IdentRefId,
    /// The referenced symbol identifier
    pub ident: Identifier,
}

impl IdentifierRef {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self { id, ident }
    }
}
