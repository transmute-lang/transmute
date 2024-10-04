use crate::identifier::Identifier;
use transmute_core::ids::{ExprId, IdentRefId, StmtId, TypeDefId};
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
    Ret(Option<ExprId>, RetMode),
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
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub span: Span,
}

impl TypeDef {
    pub fn identifier_ref_id(&self) -> IdentRefId {
        match &self.kind {
            TypeDefKind::Simple(ident_ref_id) => *ident_ref_id,
            TypeDefKind::Array(_, _) => todo!(),
            _ => panic!("no identifier_ref_id for TypeDefKind::Dummy"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDefKind {
    Simple(IdentRefId),
    Array(TypeDefId, usize),
    /// A dummy type kind, inserted by the parser when the type could not be parsed
    Dummy,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub identifier: Identifier,
    pub type_def_id: TypeDefId,
    pub span: Span,
}

impl Parameter {
    pub fn new(identifier: Identifier, type_def_id: TypeDefId, span: Span) -> Self {
        Self {
            identifier,
            type_def_id,
            span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub type_def_id: Option<TypeDefId>,
}

impl Return {
    pub fn none() -> Self {
        Self { type_def_id: None }
    }

    pub fn some(type_def_id: TypeDefId) -> Self {
        Self {
            type_def_id: Some(type_def_id),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub identifier: Identifier,
    pub type_def_id: TypeDefId,
    pub span: Span,
}

impl Field {
    pub fn new(identifier: Identifier, type_def_id: TypeDefId, span: Span) -> Self {
        Self {
            identifier,
            type_def_id,
            span,
        }
    }

    // todo:refactor remove the following methods: they are not useful as all fields are pub
    pub fn identifier(&self) -> &Identifier {
        &self.identifier
    }

    pub fn take_identifier(self) -> Identifier {
        self.identifier
    }

    pub fn type_def_id(&self) -> TypeDefId {
        self.type_def_id
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
