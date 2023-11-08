use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::StmtId;
use crate::lexer::Span;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
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

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ExprId {
    id: usize,
}

impl ExprId {
    pub fn id(&self) -> usize {
        self.id
    }
}

impl Display for ExprId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl From<usize> for ExprId {
    fn from(id: usize) -> Self {
        Self { id }
    }
}

#[derive(Debug, PartialEq)]
pub enum ExpressionKind {
    Assignment(Identifier, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Binary(ExprId, BinaryOperator, ExprId),
    FunctionCall(Identifier, Vec<ExprId>),
    Unary(UnaryOperator, ExprId),
    While(ExprId, ExprId),
    // todo: should it be it's own struct and use it like While(ExprId, Block)?
    Block(Vec<StmtId>),
}
