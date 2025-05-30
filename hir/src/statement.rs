use crate::bound::{Bound, BoundState, Unbound};
use crate::identifier::Identifier;
use crate::typed::{Typed, TypedState, Untyped};
use transmute_ast::annotation::Annotation as AstAnnotation;
use transmute_ast::statement::Field as AstField;
use transmute_ast::statement::Parameter as AstParameter;
use transmute_ast::statement::RetMode as AstRetMode;
use transmute_ast::statement::Return as AstReturn;
use transmute_ast::statement::Statement as AstStatement;
use transmute_ast::statement::StatementKind as AstStatementKind;
use transmute_ast::statement::TypeDef as AstTypeDef;
use transmute_ast::statement::TypeDefKind as AstTypeDefKind;
use transmute_core::ids::{ExprId, IdentRefId, InputId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Statement<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub id: StmtId,
    pub kind: StatementKind<T, B>,
    pub span: Span,
}

impl Statement<Typed, Bound> {
    pub fn new(
        id: StmtId,
        kind: StatementKind<Typed, Bound>,
        span: Span,
    ) -> Statement<Typed, Bound> {
        Statement::<Typed, Bound> { id, kind, span }
    }
}

impl From<AstStatement> for Statement<Untyped, Unbound> {
    fn from(value: AstStatement) -> Self {
        Self {
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
                AstStatementKind::Expression(expr_id) => StatementKind::Expression(expr_id),
                AstStatementKind::Let(identifier, expr_id) => {
                    StatementKind::Let(Identifier::from(identifier), expr_id)
                }
                AstStatementKind::Ret(expr_id, ret_mode) => {
                    StatementKind::Ret(expr_id, RetMode::from(ret_mode))
                }
                AstStatementKind::LetFn(identifier, annotations, params, ret_type, expr_id) => {
                    StatementKind::LetFn(
                        Identifier::from(identifier),
                        annotations
                            .into_iter()
                            .map(Annotation::from)
                            .collect::<Vec<Annotation>>(),
                        params
                            .into_iter()
                            .map(Parameter::from)
                            .collect::<Vec<Parameter<Untyped, Unbound>>>(),
                        Return::from(ret_type),
                        Implementation::Provided(expr_id),
                    )
                }
                AstStatementKind::Struct(identifier, annotations, fields) => StatementKind::Struct(
                    Identifier::from(identifier),
                    annotations
                        .into_iter()
                        .map(Annotation::from)
                        .collect::<Vec<Annotation>>(),
                    Implementation::Provided(
                        fields
                            .into_iter()
                            .map(Field::from)
                            .collect::<Vec<Field<Untyped, Unbound>>>(),
                    ),
                ),
                AstStatementKind::Annotation(identifier) => {
                    StatementKind::Annotation(Identifier::from(identifier))
                }
                AstStatementKind::Use(ident_ref_ids) => StatementKind::Use(ident_ref_ids),
                AstStatementKind::Namespace(identifier, input_id, statements) => {
                    StatementKind::Namespace(Identifier::from(identifier), input_id, statements)
                }
            },
        }
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
    Ret(Option<ExprId>, RetMode),
    LetFn(
        Identifier<B>,
        Vec<Annotation>,
        Vec<Parameter<T, B>>,
        Return<T>,
        Implementation<ExprId>,
    ),
    Struct(
        Identifier<B>,
        Vec<Annotation>,
        Implementation<Vec<Field<T, B>>>,
    ),
    Annotation(Identifier<B>),
    Use(Vec<IdentRefId>),
    Namespace(
        /// Namespace identifier
        Identifier<B>,
        /// `InputId` this namespace is coming from
        InputId,
        /// Statements included in this namespace
        Vec<StmtId>,
    ),
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

impl From<AstRetMode> for RetMode {
    fn from(value: AstRetMode) -> Self {
        match value {
            AstRetMode::Explicit => RetMode::Explicit,
            AstRetMode::Implicit => RetMode::Implicit,
        }
    }
}

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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDefKind {
    Simple(Vec<IdentRefId>),
    Array(TypeDefId, usize),
}

impl From<AstTypeDef> for TypeDef {
    fn from(value: AstTypeDef) -> Self {
        match value.kind {
            AstTypeDefKind::Simple(ident_ref_ids) => TypeDef {
                kind: TypeDefKind::Simple(ident_ref_ids),
                span: value.span,
            },
            AstTypeDefKind::Array(type_def_id, len) => TypeDef {
                kind: TypeDefKind::Array(type_def_id, len),
                span: value.span,
            },
            AstTypeDefKind::Dummy => panic!("Cannot convert AstType::Dummy"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub ident_ref_ids: Vec<IdentRefId>,
    pub span: Span,
}

impl From<AstAnnotation> for Annotation {
    fn from(value: AstAnnotation) -> Self {
        Annotation {
            ident_ref_ids: value.ident_ref_ids,
            span: value.span,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub identifier: Identifier<B>,
    pub type_def_id: TypeDefId,
    pub span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the parameter, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl Parameter<Untyped, Unbound> {
    /// Types and binds the parameter.
    pub fn bind(self, type_id: TypeId, symbol_id: SymbolId) -> Parameter<Typed, Bound> {
        Parameter::<Typed, Bound> {
            identifier: self.identifier.bind(symbol_id),
            type_def_id: self.type_def_id,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl From<AstParameter> for Parameter<Untyped, Unbound> {
    fn from(value: AstParameter) -> Self {
        Self {
            span: value.span.clone(),
            type_def_id: value.type_def_id,
            identifier: Identifier::from(value.identifier),
            typed: Untyped,
        }
    }
}

impl<B> Parameter<Typed, B>
where
    B: BoundState,
{
    pub fn resolved_type_id(&self) -> TypeId {
        self.typed.0
    }
}

impl<T> Parameter<T, Bound>
where
    T: TypedState,
{
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.identifier.resolved_symbol_id()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return<T>
where
    T: TypedState,
{
    pub type_def_id: Option<TypeDefId>,
    typed: T,
}

impl Return<Untyped> {
    pub fn typed(self, type_id: TypeId) -> Return<Typed> {
        Return::<Typed> {
            type_def_id: self.type_def_id,
            typed: Typed(type_id),
        }
    }
}

impl From<AstReturn> for Return<Untyped> {
    fn from(value: AstReturn) -> Self {
        Self {
            type_def_id: value.type_def_id,
            typed: Untyped,
        }
    }
}

impl Return<Typed> {
    pub fn resolved_type_id(&self) -> TypeId {
        self.typed.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub identifier: Identifier<B>,
    pub type_def_id: TypeDefId,
    pub span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the field, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl Field<Untyped, Unbound> {
    pub fn new(identifier: Identifier<Unbound>, type_def_id: TypeDefId, span: Span) -> Self {
        Self {
            identifier,
            type_def_id,
            span,
            typed: Untyped,
        }
    }
}

impl From<AstField> for Field<Untyped, Unbound> {
    fn from(value: AstField) -> Self {
        Self {
            type_def_id: value.type_def_id,
            span: value.span,
            identifier: Identifier::from(value.identifier),
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
            type_def_id: self.type_def_id,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl<B> Field<Typed, B>
where
    B: BoundState,
{
    pub fn resolved_type_id(&self) -> TypeId {
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
            type_def_id: self.type_def_id,
            span: self.span,
            typed: self.typed,
        }
    }
}

impl<T> Field<T, Bound>
where
    T: TypedState,
{
    pub fn resolved_symbol_id(&self) -> SymbolId {
        self.identifier.resolved_symbol_id()
    }
}
