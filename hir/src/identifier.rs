use crate::bound::{Bound, BoundMultiple, BoundState, Unbound};
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

impl<B> Identifier<B> where B: BoundState {}

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

    pub fn bind_multiple(self, symbol_ids: Vec<SymbolId>) -> Identifier<BoundMultiple> {
        Identifier::<BoundMultiple> {
            id: self.id,
            span: self.span,
            bound: BoundMultiple(symbol_ids),
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

impl Identifier<BoundMultiple> {
    pub fn resolved_symbol_ids(&self) -> &[SymbolId] {
        &self.bound.0
    }

    pub fn into_bound_unique(self) -> Identifier<Bound> {
        debug_assert_eq!(self.bound.0.len(), 1);
        Identifier {
            id: self.id,
            span: self.span,
            bound: Bound(self.bound.0[0]),
        }
    }
}
