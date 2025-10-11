use crate::bound::{Bound, BoundState, Unbound};
use crate::identifier::Identifier;
use crate::typed::{Typed, TypedState, Untyped};
use transmute_core::ids::{ExprId, IdentRefId, InputId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::span::Span;
use transmute_nst::nodes::Annotation as NstAnnotation;
use transmute_nst::nodes::Field as NstField;
use transmute_nst::nodes::Parameter as NstParameter;
use transmute_nst::nodes::RetMode as NstRetMode;
use transmute_nst::nodes::Return as NstReturn;
use transmute_nst::nodes::Statement as NstStatement;
use transmute_nst::nodes::StatementKind as NstStatementKind;
use transmute_nst::nodes::TypeDef as NstTypeDef;
use transmute_nst::nodes::TypeDefKind as NstTypeDefKind;

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

impl<T, B> Statement<T, B>
where
    T: TypedState,
    B: BoundState,
{
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

    #[allow(clippy::type_complexity)]
    pub fn as_struct(
        &self,
    ) -> (
        &Identifier<B>,
        &Vec<Annotation>,
        &Vec<Identifier<B>>,
        &Implementation<Vec<Field<T, B>>>,
        Option<&StmtId>,
    ) {
        match &self.kind {
            StatementKind::Struct(
                identifier,
                annotations,
                type_parameters,
                implementation,
                stmt_id,
            ) => (
                identifier,
                annotations,
                type_parameters,
                implementation,
                stmt_id.as_ref(),
            ),
            _ => panic!("struct expected, got {:?}", self),
        }
    }

    pub fn as_namespace(&self) -> (&Identifier<B>, &InputId, &Vec<StmtId>) {
        match &self.kind {
            StatementKind::Namespace(identifier, input_id, stmts) => (identifier, input_id, stmts),
            _ => panic!("namespace expected, got {:?}", self),
        }
    }

    pub fn into_namespace(self) -> (Identifier<B>, InputId, Vec<StmtId>) {
        match self.kind {
            StatementKind::Namespace(identifier, input_id, stmts) => (identifier, input_id, stmts),
            _ => panic!("namespace expected, got {:?}", self),
        }
    }
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

impl From<NstStatement> for Statement<Untyped, Unbound> {
    fn from(value: NstStatement) -> Self {
        Self {
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
                NstStatementKind::Expression(expr_id) => StatementKind::Expression(expr_id),
                NstStatementKind::Let(identifier, expr_id) => {
                    StatementKind::Let(Identifier::from(identifier), expr_id)
                }
                NstStatementKind::Ret(expr_id, ret_mode) => {
                    StatementKind::Ret(expr_id, RetMode::from(ret_mode))
                }
                NstStatementKind::LetFn(identifier, annotations, params, ret_type, expr_id) => {
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
                        None,
                    )
                }
                NstStatementKind::Struct(identifier, annotations, type_parameters, fields) => {
                    StatementKind::Struct(
                        Identifier::from(identifier),
                        annotations
                            .into_iter()
                            .map(Annotation::from)
                            .collect::<Vec<Annotation>>(),
                        type_parameters
                            .into_iter()
                            .map(Identifier::from)
                            .collect::<Vec<_>>(),
                        Implementation::Provided(
                            fields
                                .into_iter()
                                .map(Field::from)
                                .collect::<Vec<Field<Untyped, Unbound>>>(),
                        ),
                        None,
                    )
                }
                NstStatementKind::Annotation(identifier) => {
                    StatementKind::Annotation(Identifier::from(identifier))
                }
                NstStatementKind::Use(ident_ref_ids) => StatementKind::Use(ident_ref_ids),
                NstStatementKind::Namespace(identifier, input_id, statements) => {
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
        /// The `LetFn`'s `StmtId` in which the struct is defined, if a nested struct
        Option<StmtId>,
    ),
    Struct(
        Identifier<B>,
        Vec<Annotation>,
        Vec<Identifier<B>>,
        Implementation<Vec<Field<T, B>>>,
        /// The `LetFn`'s `StmtId` in which the struct is defined, if a nested struct
        Option<StmtId>,
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

impl From<NstRetMode> for RetMode {
    fn from(value: NstRetMode) -> Self {
        match value {
            NstRetMode::Explicit => RetMode::Explicit,
            NstRetMode::Implicit => RetMode::Implicit,
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

impl<T> Implementation<T> {
    pub fn get(self) -> T {
        match self {
            Implementation::Provided(fields) => fields,
            _ => panic!("implementation required"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub span: Span,
}

impl TypeDef {
    pub fn collect_ident_ref_ids(&self) -> Vec<IdentRefId> {
        match &self.kind {
            TypeDefKind::Simple(ident_ref_ids) => ident_ref_ids.clone(),
            TypeDefKind::Array(..) => Vec::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDefKind {
    Simple(Vec<IdentRefId>),
    Array(TypeDefId, usize),
}

impl From<NstTypeDef> for TypeDef {
    fn from(value: NstTypeDef) -> Self {
        match value.kind {
            NstTypeDefKind::Simple(ident_ref_ids) => TypeDef {
                kind: TypeDefKind::Simple(ident_ref_ids),
                span: value.span,
            },
            NstTypeDefKind::Array(type_def_id, len) => TypeDef {
                kind: TypeDefKind::Array(type_def_id, len),
                span: value.span,
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub ident_ref_ids: Vec<IdentRefId>,
    pub span: Span,
}

impl From<NstAnnotation> for Annotation {
    fn from(value: NstAnnotation) -> Self {
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

impl From<NstParameter> for Parameter<Untyped, Unbound> {
    fn from(value: NstParameter) -> Self {
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

impl From<NstReturn> for Return<Untyped> {
    fn from(value: NstReturn) -> Self {
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

impl From<NstField> for Field<Untyped, Unbound> {
    fn from(value: NstField) -> Self {
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
