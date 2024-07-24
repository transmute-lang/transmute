use crate::ast::identifier::Identifier;
use crate::ids::{ExprId, IdentRefId, StmtId};
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

    pub fn take_kind(self) -> StatementKind {
        self.kind
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
    identifier: Identifier,
    ty: IdentRefId,
    span: Span,
}

impl Parameter {
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
}

impl Return {
    pub fn ident_ret_id(&self) -> Option<IdentRefId> {
        self.ret
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    identifier: Identifier,
    ty: IdentRefId,
    span: Span,
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
