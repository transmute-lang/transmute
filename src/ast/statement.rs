use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, ScopeId, StmtId};
use crate::lexer::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    id: StmtId,
    kind: StatementKind,
    span: Span,
    // todo remove, this is useless
    scope: Option<ScopeId>,
}

impl Statement {
    pub fn new(id: StmtId, kind: StatementKind, span: Span) -> Self {
        Self {
            id,
            kind,
            span,
            scope: None,
        }
    }

    pub fn new_with_scope(id: StmtId, kind: StatementKind, span: Span, scope: ScopeId) -> Self {
        Self {
            id,
            kind,
            span,
            scope: Some(scope),
        }
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

    pub fn set_scope(&mut self, scope: ScopeId) {
        // todo should take a self and return a new self?
        self.scope = Some(scope);
    }

    pub fn scope(&self) -> Option<ScopeId> {
        self.scope
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(ExprId),
    // todo second Identifier should be a type
    LetFn(Identifier, Vec<Parameter>, Option<Identifier>, ExprId),
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
