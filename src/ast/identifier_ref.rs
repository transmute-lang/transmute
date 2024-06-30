use crate::ast::identifier::Identifier;
use crate::ast::ids::{IdentId, IdentRefId, SymbolId};
use crate::lexer::Span;

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef<B>
where
    B: BoundState,
{
    /// ID of this identifier reference
    id: IdentRefId,
    /// The referenced symbol identifier
    ident: Identifier,
    /// When `Bound`, the referenced `SymbolId`
    bound_state: B, // todo move to Identifier
}

impl<S> IdentifierRef<S>
where
    S: BoundState,
{
    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier {
        &self.ident
    }

    pub fn ident_id(&self) -> IdentId {
        self.ident.id()
    }

    pub fn span(&self) -> &Span {
        self.ident.span()
    }
}

impl IdentifierRef<Unbound> {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self {
            id,
            ident,
            bound_state: Unbound {},
        }
    }

    pub fn resolved(self, symbol_id: SymbolId) -> IdentifierRef<Bound> {
        IdentifierRef {
            id: self.id,
            ident: self.ident,
            bound_state: Bound(symbol_id),
        }
    }
}

impl IdentifierRef<Bound> {
    pub fn new_resolved(id: IdentRefId, ident: Identifier, symbol_id: SymbolId) -> Self {
        Self {
            id,
            ident,
            bound_state: Bound(symbol_id),
        }
    }
    pub fn symbol_id(&self) -> SymbolId {
        self.bound_state.0
    }
}

pub trait BoundState {}

#[derive(Debug, Clone, PartialEq)]
pub struct Unbound;

impl BoundState for Unbound {}

#[derive(Debug, Clone, PartialEq)]
pub struct Bound(pub SymbolId);

impl BoundState for Bound {}
