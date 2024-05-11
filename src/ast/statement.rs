use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, StmtId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    id: StmtId,
    kind: StatementKind,
    span: Span,
}

impl Statement {
    pub fn new(id: StmtId, kind: StatementKind, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn id(&self) -> StmtId {
        self.id
    }

    pub fn kind(&self) -> &StatementKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId, RetMode),
    // todo second Identifier should be a type
    LetFn(Identifier, Vec<Parameter>, Option<Identifier>, ExprId),
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
pub struct Parameter {
    identifier: Identifier,
    ty: Identifier, // todo must be something more complex (a TypeId?), but let's start simple
    span: Span,
}

impl Parameter {
    pub fn new(identifier: Identifier, ty: Identifier, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
        }
    }

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
