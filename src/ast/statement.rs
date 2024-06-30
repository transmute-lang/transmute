use crate::ast::expression::{Typed, TypedState, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, IdentRefId, StmtId, TypeId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<T>
where
    T: TypedState,
{
    id: StmtId,
    kind: StatementKind<T>,
    span: Span,
}

impl<T> Statement<T>
where
    T: TypedState,
{
    pub fn new(id: StmtId, kind: StatementKind<T>, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> StmtId {
        self.id
    }

    pub fn kind(&self) -> &StatementKind<T> {
        &self.kind
    }

    pub fn take_kind(self) -> StatementKind<T> {
        self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind<T>
where
    T: TypedState,
{
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId, RetMode),
    LetFn(Identifier, Vec<Parameter<T>>, Return, ExprId),
    Struct(Identifier, Vec<Field<T>>),
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RetMode {
    Explicit,
    Implicit,
}

impl RetMode {
    pub fn as_str(&self) -> &'static str {
        match self {
            RetMode::Explicit => "explicit",
            RetMode::Implicit => "implicit",
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter<T>
where
    T: TypedState,
{
    identifier: Identifier,
    ty: IdentRefId,
    span: Span,
    state: T, // fixme is it really needed??
}

impl<T> Parameter<T>
where
    T: TypedState,
{
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Parameter<Untyped> {
    pub fn new(identifier: Identifier, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            state: Untyped,
        }
    }

    /// Types the parameter.
    pub fn bind(self, type_id: TypeId) -> Parameter<Typed> {
        Parameter::<Typed> {
            identifier: self.identifier,
            ty: self.ty,
            span: self.span,
            state: Typed(type_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    ret: Option<IdentRefId>,
}

impl Return {
    pub fn none() -> Self {
        Self { ret: None }
    }

    pub fn some(ident_ref_id: IdentRefId) -> Self {
        Self {
            ret: Some(ident_ref_id),
        }
    }

    pub fn ident_ret_id(&self) -> Option<IdentRefId> {
        self.ret
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<T>
where
    T: TypedState,
{
    // todo add bound/type
    identifier: Identifier,
    ty: Identifier, // todo should be a IdentifierRef<B>
    span: Span,
    state: T,
}

impl Field<Untyped> {
    pub fn new(identifier: Identifier, ty: Identifier, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            state: Untyped,
        }
    }

    pub fn typed(self, type_id: TypeId) -> Field<Typed> {
        Field {
            identifier: self.identifier,
            ty: self.ty,
            span: self.span,
            state: Typed(type_id),
        }
    }
}

impl Field<Typed> {
    pub fn type_id(&self) -> TypeId {
        self.state.0
    }
}

impl<T> Field<T>
where
    T: TypedState,
{
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    pub fn ty(&self) -> &Identifier {
        &self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
