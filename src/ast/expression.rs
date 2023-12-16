use crate::ast::ids::{ExprId, IdentRefId,  StmtId};
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    id: ExprId,
    kind: ExpressionKind,
    span: Span,
}

impl Expression {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
        }
    }

    pub fn id(&self) -> ExprId {
        self.id
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionKind {
    Assignment(IdentRefId, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Binary(ExprId, BinaryOperator, ExprId),
    Unary(UnaryOperator, ExprId),
    FunctionCall(IdentRefId, Vec<ExprId>),
    While(ExprId, ExprId),
    // todo: should it be it's own struct and use it like While(ExprId, Block)?
    Block(Vec<StmtId>),
    /// A dummy expression kind, inserted by the parser when the expression could not be parsed
    // todo probably remove...
    Dummy,
}
