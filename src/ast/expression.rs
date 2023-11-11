use crate::ast::ids::{ExprId, IdentRefId, ScopeId, StmtId};
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    id: ExprId,
    kind: ExpressionKind,
    span: Span,
    scope: Option<ScopeId>,
}

impl Expression {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
            scope: None,
        }
    }

    pub fn id(&self) -> ExprId {
        self.id
    }

    pub fn kind(&self) -> &ExpressionKind {
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
pub enum ExpressionKind {
    Assignment(IdentRefId, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Binary(ExprId, BinaryOperator, ExprId),
    FunctionCall(IdentRefId, Vec<ExprId>),
    Unary(UnaryOperator, ExprId),
    While(ExprId, ExprId),
    // todo: should it be it's own struct and use it like While(ExprId, Block)?
    Block(Vec<StmtId>),
}
