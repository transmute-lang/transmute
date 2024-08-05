use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ids::{ExprId, IdentRefId, StmtId};
use crate::lexer::Span;
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    id: ExprId,
    kind: ExpressionKind,
    span: Span,
}

impl Expression {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> ExprId {
        self.id
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn take_kind(self) -> ExpressionKind {
        self.kind
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn take_span(self) -> Span {
        self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionKind {
    Assignment(Target, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Binary(ExprId, BinaryOperator, ExprId),
    Unary(UnaryOperator, ExprId),
    Access(ExprId, IdentRefId),
    FunctionCall(IdentRefId, Vec<ExprId>),
    While(ExprId, ExprId),
    Block(Vec<StmtId>),
    StructInstantiation(IdentRefId, Vec<(IdentRefId, ExprId)>),
    /// A dummy expression kind, inserted by the parser when the expression could not be parsed
    Dummy,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Target {
    Direct(IdentRefId),
    // The expression id is of kind ExpressionKind::Access
    Indirect(ExprId),
}
