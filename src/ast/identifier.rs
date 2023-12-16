use crate::ast::ids::{IdentId, IdentRefId, ScopeId, SymbolId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    id: IdentId,
    span: Span,
    scope: Option<ScopeId>,
}

impl Identifier {
    pub fn new(id: IdentId, span: Span) -> Self {
        Self {
            id,
            span,
            scope: None,
        }
    }

    pub fn id(&self) -> IdentId {
        self.id
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn set_scope(&mut self, scope: ScopeId) {
        // todo should take a self and return a new self?
        self.scope = Some(scope);
    }

    pub fn scope(&self) -> Option<ScopeId> {
        self.scope
    }
}

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef {
    id: IdentRefId,
    ident: Identifier,
    /// The referenced symbol id
    symbol_id: Option<SymbolId>,
}

impl IdentifierRef {
    pub fn new(id: IdentRefId, ident: Identifier) -> Self {
        Self {
            id,
            ident,
            symbol_id: None,
        }
    }

    pub fn id(&self) -> IdentRefId {
        self.id
    }

    pub fn ident(&self) -> &Identifier {
        &self.ident
    }

    pub fn set_symbol_id(&mut self, symbol_id: SymbolId) {
        self.symbol_id = Some(symbol_id);
    }

    pub fn symbol_id(&self) -> Option<SymbolId> {
        self.symbol_id
    }
}
