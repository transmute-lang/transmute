use crate::ast::expression::{Typed, TypedState, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{BoundState, Unbound};
use crate::ast::ids::{ExprId, IdentRefId, StmtId, TypeId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<T, B>
where
    T: TypedState,
    B: BoundState,
{
    id: StmtId,
    kind: StatementKind<T, B>,
    span: Span,
}

impl<T, B> Statement<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn new(id: StmtId, kind: StatementKind<T, B>, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> StmtId {
        self.id
    }

    pub fn kind(&self) -> &StatementKind<T, B> {
        &self.kind
    }

    pub fn take_kind(self) -> StatementKind<T, B> {
        self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind<T, B>
where
    T: TypedState,
    B: BoundState,
{
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId, RetMode),
    LetFn(Identifier, Vec<Parameter<T>>, Return<B>, ExprId),
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
pub struct Return<B>
where
    B: BoundState,
{
    // todo should be an IdentifierRef<B>, and the second element a <T>
    ret: Option<(Identifier, B)>,
}

impl<B> Return<B>
where
    B: BoundState,
{
    pub fn none() -> Self {
        Self { ret: None }
    }

    pub fn some(identifier: Identifier, state: B) -> Self {
        Self {
            ret: Some((identifier, state)),
        }
    }

    pub fn map_identifier<F>(self, f: F) -> Self
    where
        F: FnOnce(Identifier) -> Identifier,
    {
        match self.ret {
            None => self,
            Some((ident, bound)) => Self {
                ret: Some((f(ident), bound)),
            },
        }
    }

    pub fn identifier(&self) -> Option<&Identifier> {
        self.ret.as_ref().map(|(ident, _)| ident)
    }
}

impl Return<Unbound> {
    pub fn take_identifier(self) -> Option<Identifier> {
        self.ret.map(|(ident, _)| ident)
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
