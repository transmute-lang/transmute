use crate::bound::{Bound, BoundMultiple, BoundState, Unbound};
use crate::identifier::Identifier;
use std::fmt::Debug;
use transmute_core::ids::{IdentRefId, SymbolId};
use transmute_nst::nodes::IdentifierRef as NstIdentifierRef;

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
    pub fn resolved(self, symbol_id: SymbolId) -> IdentifierRef<BoundMultiple> {
        self.resolved_multiple(vec![symbol_id])
    }

    pub fn resolved_multiple(self, symbol_ids: Vec<SymbolId>) -> IdentifierRef<BoundMultiple> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.bind_multiple(symbol_ids),
        }
    }
}

impl From<NstIdentifierRef> for IdentifierRef<Unbound> {
    fn from(value: NstIdentifierRef) -> Self {
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

impl IdentifierRef<BoundMultiple> {
    pub fn resolved_symbol_ids(&self) -> &[SymbolId] {
        self.ident.resolved_symbol_ids()
    }

    pub fn into_bound_unique(self) -> IdentifierRef<Bound> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.into_bound_unique(),
        }
    }
}
