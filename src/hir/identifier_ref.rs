use crate::hir::bound::{Bound, BoundState, Unbound};
use crate::hir::identifier::Identifier;
use crate::ids::{IdentId, IdentRefId, SymbolId};
use crate::lexer::Span;
use std::fmt::Debug;

use crate::ast::identifier_ref::IdentifierRef as AstIdentifierRef;

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
            id: value.id(),
            ident: Identifier::from(value.take_ident()),
        }
    }
}

impl IdentifierRef<Bound> {
    pub fn symbol_id(&self) -> SymbolId {
        self.ident.symbol_id()
    }
}
