use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{Bound, BoundState, Unbound};
use crate::ast::ids::{ExprId, StmtId, SymbolId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<B>
where
    B: BoundState,
{
    id: StmtId,
    kind: StatementKind<B>,
    span: Span,
}

impl<B> Statement<B>
where
    B: BoundState,
{
    pub fn new(id: StmtId, kind: StatementKind<B>, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> StmtId {
        self.id
    }

    pub fn kind(&self) -> &StatementKind<B> {
        &self.kind
    }

    pub fn take_kind(self) -> StatementKind<B> {
        self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind<B>
where
    B: BoundState,
{
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId, RetMode),
    // todo second Identifier should be a type
    LetFn(Identifier, Vec<Parameter<B>>, Return<B>, ExprId),
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

// fixme what is bound? the identifier or the type??? so far it's the identifier...
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter<B>
where
    B: BoundState,
{
    identifier: Identifier,
    ty: Identifier, // todo must be something more complex (a TypeId?), but let's start simple
    span: Span,
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
