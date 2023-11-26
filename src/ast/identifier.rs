use crate::ast::ids::{IdentId, IdentRefId, SymbolId};
use crate::lexer::Span;

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
pub struct IdentifierRef {
    id: IdentRefId,
    ident: Identifier,
    /// The referenced symbol id
    // todo 1 - could a Node instead (or as well if we want to keep SymbolId)
    // todo 2 - allow for multiple symbols (overloading for functions and operators)
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
