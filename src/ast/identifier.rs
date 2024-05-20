use crate::ast::ids::{IdentId, IdentRefId, SymbolId};
use crate::lexer::Span;

/// Represents an identifier when not used a reference
#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    id: IdentId,
    span: Span,
}

impl Identifier {
    pub fn new(id: IdentId, span: Span) -> Self {
        Self { id, span }
    }

    pub fn id(&self) -> IdentId {
        self.id
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef<S = UnresolvedSymbol> {
    /// ID of this identifier reference
    id: IdentRefId,
    /// The referenced symbol identifier
    ident: Identifier,
    /// The referenced symbol id
    symbol: S,
}

impl IdentifierRef {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self {
            id,
            ident,
            symbol: UnresolvedSymbol {},
        }
    }

    pub fn resolved(&self, symbol_id: SymbolId) -> IdentifierRef<ResolvedSymbol> {
        IdentifierRef {
            id: self.id,
            ident: self.ident.clone(),
            symbol: ResolvedSymbol(symbol_id),
        }
    }
}

impl IdentifierRef<ResolvedSymbol> {
    pub fn new_resolved(id: IdentRefId, ident: Identifier, symbol_id: SymbolId) -> Self {
        Self {
            id,
            ident,
            symbol: ResolvedSymbol(symbol_id),
        }
    }
    pub fn symbol_id(&self) -> SymbolId {
        self.symbol.0
    }
}

impl<S> IdentifierRef<S> {
    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier {
        &self.ident
    }

    pub fn ident_id(&self) -> IdentId {
        self.ident.id
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnresolvedSymbol;

#[derive(Debug, Clone, PartialEq)]
pub struct ResolvedSymbol(SymbolId);
