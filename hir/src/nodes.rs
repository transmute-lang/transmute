use transmute_core::ids::{
    ExprId, IdentId, IdentRefId, InputId, StmtId, SymbolId, TypeDefId, TypeId,
};
use transmute_core::span::Span;
pub use transmute_nst::nodes::{
    Annotation, ExitPoint, ExitPoints, ExpressionKind, Literal, LiteralKind, Nst, RetMode, Target,
    TypeDef, TypeDefKind,
};

/// Represents an identifier when not used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct Identifier {
    pub id: IdentId,
    pub span: Span,
    pub symbol_id: SymbolId,
}

impl Identifier {
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.symbol_id
    }
}

/// Represents an identifier when used as a reference
#[derive(Debug, Clone, PartialEq)]
pub struct IdentifierRef {
    /// ID of this identifier reference
    pub id: IdentRefId,
    /// The referenced symbol identifier
    pub ident: Identifier,
}

impl IdentifierRef {
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.ident.resolved_symbol_id()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    pub id: ExprId,
    pub kind: ExpressionKind,
    pub span: Span,
    pub type_id: TypeId,
}

impl Expression {
    pub fn resolved_type_id(&self) -> TypeId {
        self.type_id
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Statement {
    pub id: StmtId,
    pub kind: StatementKind,
    pub span: Span,
}

impl Statement {
    pub fn collect_ident_ref_ids(&self) -> Vec<IdentRefId> {
        match &self.kind {
            StatementKind::LetFn(_, annotations, ..)
            | StatementKind::Struct(_, annotations, ..) => annotations
                .iter()
                .flat_map(|a| a.ident_ref_ids.clone())
                .collect::<Vec<_>>(),
            _ => Default::default(),
        }
    }

    pub fn as_annotation(&self) -> &Identifier {
        match &self.kind {
            StatementKind::Annotation(ident) => ident,
            _ => panic!("annotation expected, got {:?}", self),
        }
    }

    pub fn as_namespace(&self) -> (&Identifier, &InputId, &Vec<StmtId>) {
        match &self.kind {
            StatementKind::Namespace(identifier, input_id, stmts) => (identifier, input_id, stmts),
            _ => panic!("namespace expected, got {:?}", self),
        }
    }

    pub fn into_namespace(self) -> (Identifier, InputId, Vec<StmtId>) {
        match self.kind {
            StatementKind::Namespace(identifier, input_id, stmts) => (identifier, input_id, stmts),
            _ => panic!("namespace expected, got {:?}", self),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(Option<ExprId>, RetMode),
    LetFn(
        Identifier,
        Vec<Annotation>,
        Vec<Parameter>,
        Return,
        Implementation<ExprId>,
        /// The `LetFn`'s `StmtId` in which the function is defined, if a nested function
        Option<StmtId>,
    ),
    Struct(
        Identifier,
        Vec<Annotation>,
        Implementation<Vec<Field>>,
        /// The `LetFn`'s `StmtId` in which the struct is defined, if a nested struct
        Option<StmtId>,
    ),
    Annotation(Identifier),
    Use(Vec<IdentRefId>),
    Namespace(
        /// Namespace identifier
        Identifier,
        /// `InputId` this namespace is coming from
        InputId,
        /// Statements included in this namespace
        Vec<StmtId>,
    ),
}

// todo:refactoring check if two native are still useful
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Implementation<T> {
    /// Denotes an implementation that is provided as transmute source code
    Provided(T),
    #[cfg(not(debug_assertions))]
    /// Denotes an implementation that is provided through FFI
    Native,
    #[cfg(debug_assertions)]
    /// Denotes an implementation that is provided through FFI
    Native(T),
}

impl<T> Implementation<T> {
    pub fn get(self) -> T {
        match self {
            Implementation::Provided(fields) => fields,
            _ => panic!("implementation required"),
        }
    }

    pub fn get_ref(&self) -> &T {
        match self {
            Implementation::Provided(fields) => fields,
            _ => panic!("implementation required"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    pub identifier: Identifier,
    pub type_def_id: TypeDefId,
    pub span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the parameter, as derived from the `ty` during
    /// resolution
    pub type_id: TypeId,
}

impl Parameter {
    pub fn resolved_type_id(&self) -> TypeId {
        self.type_id
    }

    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.identifier.resolved_symbol_id()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return {
    pub type_def_id: Option<TypeDefId>,
    pub typed_id: TypeId,
}

impl Return {
    pub fn resolved_type_id(&self) -> TypeId {
        self.typed_id
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub identifier: Identifier,
    pub type_def_id: TypeDefId,
    pub span: Span,
    pub type_id: TypeId,
}

impl Field {
    pub fn resolved_type_id(&self) -> TypeId {
        self.type_id
    }

    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.identifier.resolved_symbol_id()
    }
}
