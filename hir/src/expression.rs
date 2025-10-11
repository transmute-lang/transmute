use crate::literal::{Literal, LiteralKind};
use crate::typed::{Typed, TypedState, Untyped};
use std::fmt::Debug;
use transmute_core::ids::{ExprId, IdentRefId, StmtId, TypeDefId, TypeId};
use transmute_core::span::Span;
use transmute_nst::nodes::Expression as NstExpression;
use transmute_nst::nodes::ExpressionKind as NstExpressionKind;
use transmute_nst::nodes::Target as NstTarget;

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
            ExpressionKind::StructInstantiation(ident_ref_id, type_parameters, fields) => {
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

impl From<NstExpression> for Expression<Untyped> {
    fn from(value: NstExpression) -> Self {
        Self {
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
                NstExpressionKind::Assignment(target, expr_id) => {
                    ExpressionKind::Assignment(Target::from(target), expr_id)
                }
                NstExpressionKind::If(cond, true_branch, false_branch) => {
                    ExpressionKind::If(cond, true_branch, false_branch)
                }
                NstExpressionKind::Literal(literal) => {
                    ExpressionKind::Literal(Literal::from(literal))
                }
                NstExpressionKind::Access(expr_id, ident_ref_id) => {
                    ExpressionKind::Access(expr_id, ident_ref_id)
                }
                NstExpressionKind::FunctionCall(expr_id, expr_ids) => {
                    ExpressionKind::FunctionCall(expr_id, expr_ids)
                }
                NstExpressionKind::While(cond, expr_id) => ExpressionKind::While(cond, expr_id),
                NstExpressionKind::Block(expr_ids) => ExpressionKind::Block(expr_ids),
                NstExpressionKind::StructInstantiation(ident_ref_id, type_parameters, fields) => {
                    ExpressionKind::StructInstantiation(ident_ref_id, type_parameters, fields)
                }
                NstExpressionKind::ArrayInstantiation(values) => {
                    ExpressionKind::ArrayInstantiation(values)
                }
                NstExpressionKind::ArrayAccess(expr, index) => {
                    ExpressionKind::ArrayAccess(expr, index)
                }
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
    StructInstantiation(IdentRefId, Vec<TypeDefId>, Vec<(IdentRefId, ExprId)>),
    ArrayInstantiation(Vec<ExprId>),
    ArrayAccess(ExprId, ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Target {
    Direct(IdentRefId),
    // The expression id is of kind ExpressionKind::Access
    Indirect(ExprId),
}

impl From<NstTarget> for Target {
    fn from(value: NstTarget) -> Self {
        match value {
            NstTarget::Direct(ident_ref_id) => Self::Direct(ident_ref_id),
            NstTarget::Indirect(expr_id) => Self::Indirect(expr_id),
        }
    }
}
