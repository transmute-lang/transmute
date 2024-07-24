use crate::ids::{ExprId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::statement::Field as AstField;
use crate::ast::statement::Parameter as AstParameter;
use crate::ast::statement::RetMode as AstRetMode;
use crate::ast::statement::Return as AstReturn;
use crate::ast::statement::Statement as AstStatement;
use crate::ast::statement::StatementKind as AstStatementKind;
use crate::hir::bound::{Bound, BoundState, Unbound};
use crate::hir::identifier::Identifier;
use crate::hir::typed::{Typed, TypedState, Untyped};
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
            id: value.id(),
            span: value.span().clone(),
            kind: match value.take_kind() {
                AstStatementKind::Expression(expr_id) => StatementKind::Expression(expr_id),
                AstStatementKind::Let(identifier, expr_id) => {
                    StatementKind::Let(Identifier::from(identifier), expr_id)
                }
                AstStatementKind::Ret(expr_id, ret_mode) => {
                    StatementKind::Ret(expr_id, RetMode::from(ret_mode))
                }
                AstStatementKind::LetFn(identifier, params, ret_type, expr_id) => {
                    StatementKind::LetFn(
                        Identifier::from(identifier),
                        params
                            .into_iter()
                            .map(Parameter::from)
                            .collect::<Vec<Parameter<Untyped, Unbound>>>(),
                        Return::from(ret_type),
                        expr_id,
                    )
                }
                AstStatementKind::Struct(identifier, fields) => StatementKind::Struct(
                    Identifier::from(identifier),
                    fields
                        .into_iter()
                        .map(Field::from)
                        .collect::<Vec<Field<Untyped, Unbound>>>(),
                ),
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
    Ret(ExprId, RetMode),
    LetFn(Identifier<B>, Vec<Parameter<T, B>>, Return<T>, ExprId),
    Struct(Identifier<B>, Vec<Field<T, B>>),
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

#[derive(Debug, Clone, PartialEq)]
pub struct Parameter<T, B>
where
    T: TypedState,
    B: BoundState,
{
    identifier: Identifier<B>,
    ty: IdentRefId,
    span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the parameter, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl<T, B> Parameter<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn identifier(&self) -> &Identifier<B> {
        &self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Parameter<Untyped, Unbound> {
    /// Types and binds the parameter.
    pub fn bind(self, type_id: TypeId, symbol_id: SymbolId) -> Parameter<Typed, Bound> {
        Parameter::<Typed, Bound> {
            identifier: self.identifier.bind(symbol_id),
            ty: self.ty,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl From<AstParameter> for Parameter<Untyped, Unbound> {
    fn from(value: AstParameter) -> Self {
        Self {
            span: value.span().clone(),
            ty: value.ty(),
            identifier: Identifier::from(value.take_identifier()),
            typed: Untyped,
        }
    }
}

impl<B> Parameter<Typed, B>
where
    B: BoundState,
{
    pub fn type_id(&self) -> TypeId {
        self.typed.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Return<T>
where
    T: TypedState,
{
    ret: Option<IdentRefId>,
    typed: T,
}

impl Return<Untyped> {
    pub fn typed(self, type_id: TypeId) -> Return<Typed> {
        Return::<Typed> {
            ret: self.ret,
            typed: Typed(type_id),
        }
    }
}

impl From<AstReturn> for Return<Untyped> {
    fn from(value: AstReturn) -> Self {
        Self {
            ret: value.ident_ret_id(),
            typed: Untyped,
        }
    }
}

impl<T> Return<T>
where
    T: TypedState,
{
    pub fn ident_ret_id(&self) -> Option<IdentRefId> {
        self.ret
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Field<T, B>
where
    T: TypedState,
    B: BoundState,
{
    identifier: Identifier<B>,
    ty: IdentRefId,
    span: Span,
    /// When `Typed`, corresponds to the `TypeId` of the field, as derived from the `ty` during
    /// resolution
    typed: T,
}

impl Field<Untyped, Unbound> {
    pub fn new(identifier: Identifier<Unbound>, ty: IdentRefId, span: Span) -> Self {
        Self {
            identifier,
            ty,
            span,
            typed: Untyped,
        }
    }
}

impl From<AstField> for Field<Untyped, Unbound> {
    fn from(value: AstField) -> Self {
        Self {
            ty: value.ty(),
            span: value.span().clone(),
            identifier: Identifier::from(value.take_identifier()),
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
            ty: self.ty,
            span: self.span,
            typed: Typed(type_id),
        }
    }
}

impl<B> Field<Typed, B>
where
    B: BoundState,
{
    pub fn type_id(&self) -> TypeId {
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
            ty: self.ty,
            span: self.span,
            typed: self.typed,
        }
    }
}

impl<T, B> Field<T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn identifier(&self) -> &Identifier<B> {
        &self.identifier
    }

    pub fn ty(&self) -> IdentRefId {
        self.ty
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
