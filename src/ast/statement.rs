use crate::ast::expression::{Typed, TypedState, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{Bound, BoundState, Unbound};
use crate::ast::ids::{ExprId, StmtId, SymbolId, TypeId};
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
    LetFn(Identifier, Vec<Parameter<B>>, Return<B>, ExprId),
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
pub struct Parameter<B>
where
    B: BoundState,
{
    identifier: Identifier,
    ty: Identifier, // todo should be an IdentifierRef
    span: Span,
    // todo the ty should be <B>, the state should be <T>
    state: B,
}

impl<B> Parameter<B>
where
    B: BoundState,
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

    /// Binds the parameter to a symbol in the symbol table. The `symbol_id` is the parameter's
    /// symbol id.
    pub fn bind(self, symbol_id: SymbolId) -> Parameter<Bound> {
        Parameter::<Bound> {
            identifier: self.identifier,
            ty: self.ty,
            span: self.span,
            state: Bound(symbol_id),
        }
    }
}

impl Parameter<Unbound> {
    pub fn new(identifier: Identifier, ty: Identifier, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            state: Unbound,
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
