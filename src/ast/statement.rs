use crate::ast::expression::{Typed, TypedState, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{Bound, BoundState, Unbound};
use crate::ast::ids::{ExprId, IdentRefId, StmtId, SymbolId, TypeId};
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
    Let(Identifier<B>, ExprId),
    Ret(ExprId, RetMode),
    LetFn(Identifier<B>, Vec<Parameter<T, B>>, Return<T>, ExprId),
    Struct(Identifier<B>, Vec<Field<T, B>>),
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
pub struct Parameter<T, B>
where
    T: TypedState,
    B: BoundState,
{
    identifier: Identifier<B>,
    ty: IdentRefId,
    span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the parameter, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl<T, B> Parameter<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn identifier(&self) -> &Identifier<B> {
        &self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Parameter<Untyped, Unbound> {
    pub fn new(identifier: Identifier<Unbound>, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            typed: Untyped,
        }
    }

    /// Types and binds the parameter.
    pub fn bind(self, type_id: TypeId, symbol_id: SymbolId) -> Parameter<Typed, Bound> {
        Parameter::<Typed, Bound> {
            identifier: self.identifier.bind(symbol_id),
            ty: self.ty,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl<B> Parameter<Typed, B>
where
    B: BoundState,
{
    pub fn type_id(&self) -> TypeId {
        self.typed.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return<T>
where
    T: TypedState,
{
    ret: Option<IdentRefId>,
    typed: T,
}

impl Return<Untyped> {
    pub fn none() -> Self {
        Self {
            ret: None,
            typed: Untyped,
        }
    }

    pub fn some(ident_ref_id: IdentRefId) -> Self {
        Self {
            ret: Some(ident_ref_id),
            typed: Untyped,
        }
    }

    pub fn typed(self, type_id: TypeId) -> Return<Typed> {
        Return::<Typed> {
            ret: self.ret,
            typed: Typed(type_id),
        }
    }
}

impl<T> Return<T>
where
    T: TypedState,
{
    pub fn ident_ret_id(&self) -> Option<IdentRefId> {
        self.ret
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<T, B>
where
    T: TypedState,
    B: BoundState,
{
    identifier: Identifier<B>,
    ty: IdentRefId,
    span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the field, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl Field<Untyped, Unbound> {
    pub fn new(identifier: Identifier<Unbound>, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            typed: Untyped,
        }
    }
}

impl<B> Field<Untyped, B>
where
    B: BoundState,
{
    pub fn typed(self, type_id: TypeId) -> Field<Typed, B> {
        Field {
            identifier: self.identifier,
            ty: self.ty,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl<B> Field<Typed, B>
where
    B: BoundState,
{
    pub fn type_id(&self) -> TypeId {
        self.typed.0
    }
}

impl<T> Field<T, Unbound>
where
    T: TypedState,
{
    pub fn bind(self, symbol_id: SymbolId) -> Field<T, Bound> {
        Field {
            identifier: self.identifier.bind(symbol_id),
            ty: self.ty,
            span: self.span,
            typed: self.typed,
        }
    }
}

impl<T, B> Field<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn identifier(&self) -> &Identifier<B> {
        &self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
