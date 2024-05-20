use crate::ast::identifier::Identifier;
use crate::ast::ids::{IdentId, IdentRefId, SymbolId};

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef<S> {
    /// ID of this identifier reference
    id: IdentRefId,
    /// The referenced symbol identifier
    ident: Identifier,
    /// The referenced symbol id
    symbol: S,
}

impl<S> IdentifierRef<S> {
    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier {
        &self.ident
    }

    pub fn ident_id(&self) -> IdentId {
        self.ident.id()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Unresolved;

impl IdentifierRef<Unresolved> {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self {
            id,
            ident,
            symbol: Unresolved {},
        }
    }

    pub fn resolved(&self, symbol_id: SymbolId) -> IdentifierRef<Resolved> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.clone(),
            symbol: Resolved(symbol_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Resolved(SymbolId);
impl IdentifierRef<Resolved> {
    pub fn new_resolved(id: IdentRefId, ident: Identifier, symbol_id: SymbolId) -> Self {
        Self {
            id,
            ident,
            symbol: Resolved(symbol_id),
        }
    }
    pub fn symbol_id(&self) -> SymbolId {
        self.symbol.0
    }
}
