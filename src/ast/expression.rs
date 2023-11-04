use crate::ast::identifier::Identifier;
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::StmtId;
use crate::lexer::Span;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub struct Expression<'s> {
    id: ExprId,
    kind: ExpressionKind<'s>,
    span: Span,
}

impl<'s> Expression<'s> {
    pub fn new(id: ExprId, kind: ExpressionKind<'s>, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> ExprId {
        self.id
    }

    pub fn kind(&self) -> &ExpressionKind<'s> {
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

// todo vec does not hold span and position as it should
#[derive(Debug, PartialEq)]
pub enum ExpressionKind<'s> {
    Assignment(Identifier<'s>, ExprId),
    If(ExprId, Vec<StmtId>, Option<Vec<StmtId>>),
    Literal(Literal<'s>),
    Binary(ExprId, BinaryOperator, ExprId),
    FunctionCall(Identifier<'s>, Vec<ExprId>),
    Unary(UnaryOperator, ExprId),
    While(ExprId, Vec<StmtId>),
}
