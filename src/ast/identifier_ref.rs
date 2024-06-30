use std::fmt::{Debug, Formatter};
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
    ident: Identifier<B>,
}

impl<B> IdentifierRef<B>
where
    B: BoundState,
{
    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier<B> {
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
    pub fn new(id: IdentRefId, ident: Identifier<Unbound>) -> Self {
        Self { id, ident }
    }

    pub fn resolved(self, symbol_id: SymbolId) -> IdentifierRef<Bound> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.bind(symbol_id),
        }
    }
}

impl IdentifierRef<Bound> {
    pub fn new(id: IdentRefId, ident: Identifier<Bound>) -> Self {
        Self { id, ident }
    }
    pub fn symbol_id(&self) -> SymbolId {
        self.ident.symbol_id()
    }
}

pub trait BoundState {}

#[derive(Debug, Clone, PartialEq)]
pub struct Unbound;

impl BoundState for Unbound {}

#[derive(Clone, PartialEq)]
pub struct Bound(pub SymbolId);

impl BoundState for Bound {}

impl Debug for Bound {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bound({})", self.0)
    }
}