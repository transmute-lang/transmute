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
    typed_state: T,
}

impl Expression<Untyped> {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
            typed_state: Untyped,
        }
    }

    pub fn typed(self, ty: TypeId) -> Expression<Typed> {
        Expression {
            id: self.id,
            kind: self.kind,
            span: self.span,
            typed_state: Typed(ty),
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
    pub fn ty_id(&self) -> TypeId {
        self.typed_state.0
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
    StructInstantiation(IdentRefId, Vec<(IdentRefId, ExprId)>),
    /// A dummy expression kind, inserted by the parser when the expression could not be parsed
    // todo probably remove...
    Dummy,
}

pub trait TypedState {}

#[derive(Debug)]
pub struct Untyped;

impl TypedState for Untyped {}

#[derive(Debug, Clone)]
pub struct Typed(pub TypeId);
impl TypedState for Typed {}
