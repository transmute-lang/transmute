use crate::literal::{Literal, LiteralKind};
use crate::typed::{Typed, TypedState, Untyped};
use std::fmt::Debug;
use transmute_ast::expression::Expression as AstExpression;
use transmute_ast::expression::ExpressionKind as AstExpressionKind;
use transmute_ast::expression::Target as AstTarget;
use transmute_core::ids::{ExprId, IdentRefId, StmtId, TypeId};
use transmute_core::span::Span;

#[derive(Debug, Clone, PartialEq)]
pub struct Expression<T>
where
    T: TypedState,
{
    pub id: ExprId,
    pub kind: ExpressionKind,
    pub span: Span,
    typed: T,
}

impl<T> Expression<T>
where
    T: TypedState,
{
    pub fn collect_ident_ref_ids(&self) -> Vec<IdentRefId> {
        match &self.kind {
            ExpressionKind::Assignment(Target::Direct(ident_ref_id), _) => {
                vec![*ident_ref_id]
            }
            ExpressionKind::Literal(lit) => match &lit.kind {
                LiteralKind::Identifier(ident_ref_id) => vec![*ident_ref_id],
                _ => Default::default(),
            },
            ExpressionKind::Access(_, ident_ref_id) => vec![*ident_ref_id],
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                let mut ident_ref_ids = fields
                    .iter()
                    .map(|(ident_ref_id, _)| *ident_ref_id)
                    .collect::<Vec<_>>();
                ident_ref_ids.push(*ident_ref_id);
                ident_ref_ids
            }
            _ => Default::default(),
        }
    }
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
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
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
                AstExpressionKind::FunctionCall(expr_id, expr_ids) => {
                    ExpressionKind::FunctionCall(expr_id, expr_ids)
                }
                AstExpressionKind::While(cond, expr_id) => ExpressionKind::While(cond, expr_id),
                AstExpressionKind::Block(expr_ids) => ExpressionKind::Block(expr_ids),
                AstExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                    ExpressionKind::StructInstantiation(ident_ref_id, fields)
                }
                AstExpressionKind::ArrayInstantiation(values) => {
                    ExpressionKind::ArrayInstantiation(values)
                }
                AstExpressionKind::ArrayAccess(expr, index) => {
                    ExpressionKind::ArrayAccess(expr, index)
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

impl Expression<Typed> {
    pub fn resolved_type_id(&self) -> TypeId {
        self.typed.0
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExpressionKind {
    Assignment(Target, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Access(ExprId, IdentRefId),
    FunctionCall(ExprId, Vec<ExprId>),
    While(ExprId, ExprId),
    Block(Vec<StmtId>),
    StructInstantiation(IdentRefId, Vec<(IdentRefId, ExprId)>),
    ArrayInstantiation(Vec<ExprId>),
    ArrayAccess(ExprId, ExprId),
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
