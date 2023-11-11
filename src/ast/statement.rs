use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, ScopeId, StmtId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    id: StmtId,
    // todo should be merged with Expression, maybe?
    kind: StatementKind,
    span: Span,
    scope: Option<ScopeId>,
}

impl Statement {
    pub fn new(id: StmtId, kind: StatementKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
            scope: None,
        }
    }

    pub fn id(&self) -> StmtId {
        self.id
    }

    pub fn kind(&self) -> &StatementKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn set_scope(&mut self, symbols: ScopeId) {
        // todo should take a self and return a new self?
        self.scope = Some(symbols);
    }

    pub fn scope(&self) -> Option<ScopeId> {
        self.scope
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId),
    LetFn(Identifier, Vec<Identifier>, ExprId),
}
