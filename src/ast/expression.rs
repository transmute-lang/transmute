use std::fmt::{Debug, Formatter};
use crate::ast::ids::{ExprId, IdentRefId, StmtId, TypeId};
use crate::ast::literal::Literal;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<T>
where
    T: TypedState,
{
    id: ExprId,
    kind: ExpressionKind,
    span: Span,
    typed: T,
}

impl Expression<Untyped> {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
            typed: Untyped,
        }
    }

    pub fn typed(self, ty: TypeId) -> Expression<Typed> {
        Expression {
            id: self.id,
            kind: self.kind,
            span: self.span,
            typed: Typed(ty),
        }
    }
}

impl<T> Expression<T>
where
    T: TypedState,
{
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

impl Expression<Typed> {
    pub fn type_id(&self) -> TypeId {
        self.typed.0
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
    // todo probably remove...
    Dummy,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Target {
    Direct(IdentRefId),
    // The expression id if of kind ExpressionKind::Access
    Indirect(ExprId),
}

pub trait TypedState {}

#[derive(Debug)]
pub struct Untyped;

impl TypedState for Untyped {}

#[derive(Clone)]
pub struct Typed(pub TypeId);

impl TypedState for Typed {}

impl Debug for Typed {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Typed({})", self.0)
    }
}
