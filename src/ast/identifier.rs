use crate::ast::identifier_ref::{Bound, BoundState, Unbound};
use crate::ast::ids::{IdentId, SymbolId};
use crate::lexer::Span;

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
