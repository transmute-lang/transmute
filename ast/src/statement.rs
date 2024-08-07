use crate::identifier::Identifier;
use transmute_core::ids::{ExprId, IdentRefId, StmtId};
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    pub id: StmtId,
    pub kind: StatementKind,
    pub span: Span,
}

impl Statement {
    pub fn new(id: StmtId, kind: StatementKind, span: Span) -> Self {
        Self { id, kind, span }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId, RetMode),
    LetFn(Identifier, Vec<Parameter>, Return, ExprId),
    Struct(Identifier, Vec<Field>),
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
    pub identifier: Identifier,
    pub ty: IdentRefId,
    pub span: Span,
}

impl Parameter {
    pub fn new(identifier: Identifier, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub ret: Option<IdentRefId>,
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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub identifier: Identifier,
    pub ty: IdentRefId,
    pub span: Span,
}

impl Field {
    pub fn new(identifier: Identifier, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
        }
    }

    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    pub fn take_identifier(self) -> Identifier {
        self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
