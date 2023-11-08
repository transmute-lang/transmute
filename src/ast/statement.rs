use crate::ast::expression::ExprId;
use crate::ast::identifier::Identifier;
use crate::lexer::Span;
use crate::symbol_table::ScopeId;
use std::fmt::{Display, Formatter};

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
        self.scope = Some(symbols);
    }

    pub fn scope(&self) -> Option<ScopeId> {
        self.scope
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct StmtId {
    id: usize,
}

impl StmtId {
    pub fn id(&self) -> usize {
        self.id
    }
}

impl Display for StmtId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl From<usize> for StmtId {
    fn from(id: usize) -> Self {
        Self { id }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId),
    // todo vec does not hold span and position as it should (search for "Vec<Statement>, Span")
    LetFn(Identifier, Vec<Identifier>, ExprId),
}
