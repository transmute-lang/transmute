use crate::bound::{Bound, BoundState, Unbound};
use transmute_ast::identifier::Identifier as AstIdentifier;
use transmute_core::ids::{IdentId, SymbolId};
use transmute_core::span::Span;

/// Represents an identifier when not used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct Identifier<B>
where
    B: BoundState,
{
    id: IdentId,
    span: Span,
    bound: B,
}

impl Identifier<Unbound> {
    pub fn bind(self, symbol_id: SymbolId) -> Identifier<Bound> {
        Identifier::<Bound> {
            id: self.id,
            span: self.span,
            bound: Bound(symbol_id),
        }
    }
}

impl From<AstIdentifier> for Identifier<Unbound> {
    fn from(value: AstIdentifier) -> Self {
        Identifier {
            id: value.id(),
            span: value.take_span(),
            bound: Unbound,
        }
    }
}

impl Identifier<Bound> {
    pub fn symbol_id(&self) -> SymbolId {
        self.bound.0
    }
}

impl<B> Identifier<B>
where
    B: BoundState,
{
    pub fn id(&self) -> IdentId {
        self.id
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
