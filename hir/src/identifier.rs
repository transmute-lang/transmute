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
    pub id: IdentId,
    pub span: Span,
    bound: B,
}

impl Identifier<Unbound> {
    pub fn new(id: IdentId, span: Span) -> Self {
        Self {
            id,
            span,
            bound: Unbound,
        }
    }

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
            id: value.id,
            span: value.span,
            bound: Unbound,
        }
    }
}

impl Identifier<Bound> {
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.bound.0
    }
}
