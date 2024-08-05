use crate::ast::expression::Expression as AstExpression;
use crate::ast::expression::ExpressionKind as AstExpressionKind;
use crate::ast::expression::Target as AstTarget;
use crate::hir::literal::Literal;
use crate::hir::typed::{Typed, TypedState, Untyped};
use crate::ids::{ExprId, IdentRefId, StmtId, TypeId};
use crate::lexer::Span;
use std::fmt::Debug;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<T>
where
    T: TypedState,
{
    id: ExprId,
    kind: ExpressionKind,
    span: Span,
    typed: T,
}

impl Expression<Untyped> {
    pub fn typed(self, ty: TypeId) -> Expression<Typed> {
        Expression {
            id: self.id,
            kind: self.kind,
            span: self.span,
            typed: Typed(ty),
        }
    }
}

impl From<AstExpression> for Expression<Untyped> {
    fn from(value: AstExpression) -> Self {
        Self {
            id: value.id(),
            span: value.span().clone(),
            kind: match value.take_kind() {
                AstExpressionKind::Assignment(target, expr_id) => {
                    ExpressionKind::Assignment(Target::from(target), expr_id)
                }
                AstExpressionKind::If(cond, true_branch, false_branch) => {
                    ExpressionKind::If(cond, true_branch, false_branch)
                }
                AstExpressionKind::Literal(literal) => {
                    ExpressionKind::Literal(Literal::from(literal))
                }
                AstExpressionKind::Access(expr_id, ident_ref_id) => {
                    ExpressionKind::Access(expr_id, ident_ref_id)
                }
                AstExpressionKind::FunctionCall(ident_ref_id, expr_ids) => {
                    ExpressionKind::FunctionCall(ident_ref_id, expr_ids)
                }
                AstExpressionKind::While(cond, expr_id) => ExpressionKind::While(cond, expr_id),
                AstExpressionKind::Block(expr_ids) => ExpressionKind::Block(expr_ids),
                AstExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                    ExpressionKind::StructInstantiation(ident_ref_id, fields)
                }
                AstExpressionKind::Unary(_, _) => panic!("Cannot convert AstExpressionKind::Unary"),
                AstExpressionKind::Binary(_, _, _) => {
                    panic!("Cannot convert AstExpressionKind::Binary")
                }
                AstExpressionKind::Dummy => panic!("Cannot convert AstExpressionKind::Dummy"),
            },
            typed: Untyped,
        }
    }
}

impl<T> Expression<T>
where
    T: TypedState,
{
    pub fn id(&self) -> ExprId {
        self.id
    }

    pub fn kind(&self) -> &ExpressionKind {
        &self.kind
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

impl Expression<Typed> {
    pub fn type_id(&self) -> TypeId {
        self.typed.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionKind {
    Assignment(Target, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Access(ExprId, IdentRefId),
    FunctionCall(IdentRefId, Vec<ExprId>),
    While(ExprId, ExprId),
    Block(Vec<StmtId>),
    StructInstantiation(IdentRefId, Vec<(IdentRefId, ExprId)>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Target {
    Direct(IdentRefId),
    // The expression id is of kind ExpressionKind::Access
    Indirect(ExprId),
}

impl From<AstTarget> for Target {
    fn from(value: AstTarget) -> Self {
        match value {
            AstTarget::Direct(ident_ref_id) => Self::Direct(ident_ref_id),
            AstTarget::Indirect(expr_id) => Self::Indirect(expr_id),
        }
    }
}
