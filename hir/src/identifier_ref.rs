use crate::bound::{Bound, BoundState, Unbound};
use crate::identifier::Identifier;
use std::fmt::Debug;
use transmute_ast::identifier_ref::IdentifierRef as AstIdentifierRef;
use transmute_core::ids::{IdentRefId, SymbolId};

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef<B>
where
    B: BoundState,
{
    /// ID of this identifier reference
    pub id: IdentRefId,
    /// The referenced symbol identifier
    pub ident: Identifier<B>,
}

impl IdentifierRef<Unbound> {
    pub fn resolved(self, symbol_id: SymbolId) -> IdentifierRef<Bound> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.bind(symbol_id),
        }
    }
}

impl From<AstIdentifierRef> for IdentifierRef<Unbound> {
    fn from(value: AstIdentifierRef) -> Self {
        Self {
            id: value.id,
            ident: Identifier::from(value.ident),
        }
    }
}

impl IdentifierRef<Bound> {
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.ident.resolved_symbol_id()
    }
}
