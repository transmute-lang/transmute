use crate::literal::Literal;
use crate::operators::{BinaryOperator, UnaryOperator};
use std::fmt::Debug;
use transmute_core::ids::{ExprId, IdentRefId, StmtId};
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    pub id: ExprId,
    pub kind: ExpressionKind,
    pub span: Span,
}

impl Expression {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self { id, kind, span }
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
