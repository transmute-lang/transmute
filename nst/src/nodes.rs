use std::fmt::Debug;
pub use transmute_ast::annotation::Annotation;
use transmute_ast::expression::Expression as AstExpression;
use transmute_ast::expression::ExpressionKind as AstExpressionKind;
pub use transmute_ast::expression::Target;
pub use transmute_ast::identifier::Identifier;
pub use transmute_ast::identifier_ref::IdentifierRef;
pub use transmute_ast::literal::Literal;
pub use transmute_ast::literal::LiteralKind;
pub use transmute_ast::statement::Field;
pub use transmute_ast::statement::Parameter;
pub use transmute_ast::statement::RetMode;
pub use transmute_ast::statement::Return;
use transmute_ast::statement::Statement as AstStatement;
use transmute_ast::statement::StatementKind as AstStatementKind;
pub use transmute_ast::statement::TypeDef as AstTypeDef;
pub use transmute_ast::statement::TypeDefKind as AstTypeDefKind;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, InputId, StmtId, TypeDefId};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;

#[derive(Debug, PartialEq)]
pub struct Nst {
    /// Unique identifiers names
    pub identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    /// All expressions
    pub expressions: VecMap<ExprId, Expression>,
    /// All statements
    pub statements: VecMap<StmtId, Statement>,
    /// Types
    pub type_defs: VecMap<TypeDefId, TypeDef>,
    /// Root statement
    pub root: StmtId,
    /// All exit points
    pub exit_points: ExitPoints,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expression {
    pub id: ExprId,
    pub kind: ExpressionKind,
    pub span: Span,
}

impl Expression {
    pub fn new(id: ExprId, kind: ExpressionKind, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn as_block(&self) -> &Vec<StmtId> {
        match &self.kind {
            ExpressionKind::Block(stmts) => stmts,
            _ => panic!("{:?} is not a block", self),
        }
    }
}

impl From<AstExpression> for Expression {
    fn from(value: AstExpression) -> Self {
        Self {
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
                AstExpressionKind::Assignment(target, expr_id) => {
                    ExpressionKind::Assignment(target, expr_id)
                }
                AstExpressionKind::If(cond, true_branch, false_branch) => {
                    ExpressionKind::If(cond, true_branch, false_branch)
                }
                AstExpressionKind::Literal(literal) => ExpressionKind::Literal(literal),
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
        }
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
pub struct Statement {
    pub id: StmtId,
    pub kind: StatementKind,
    pub span: Span,
}

impl Statement {
    pub fn new(id: StmtId, kind: StatementKind, span: Span) -> Self {
        Self { id, kind, span }
    }

    pub fn as_namespace(&self) -> (&Identifier, InputId, &[StmtId]) {
        match &self.kind {
            StatementKind::Namespace(identifier, input_id, stmts) => (identifier, *input_id, stmts),
            _ => panic!("{:?} is not a namespace", self),
        }
    }
}

impl From<AstStatement> for Statement {
    fn from(value: AstStatement) -> Self {
        Self {
            id: value.id,
            span: value.span.clone(),
            kind: match value.kind {
                AstStatementKind::Expression(expr_id) => StatementKind::Expression(expr_id),
                AstStatementKind::Let(identifier, expr_id) => {
                    StatementKind::Let(identifier, expr_id)
                }
                AstStatementKind::Ret(expr_id, ret_mode) => StatementKind::Ret(expr_id, ret_mode),
                AstStatementKind::LetFn(identifier, annotations, params, ret_type, expr_id) => {
                    StatementKind::LetFn(identifier, annotations, params, ret_type, expr_id)
                }
                AstStatementKind::Struct(identifier, annotations, fields) => {
                    StatementKind::Struct(identifier, annotations, fields)
                }
                AstStatementKind::Annotation(identifier) => StatementKind::Annotation(identifier),
                AstStatementKind::Use(ident_ref_ids) => StatementKind::Use(ident_ref_ids),
                AstStatementKind::Namespace(identifier, input_id, statements) => {
                    StatementKind::Namespace(identifier, input_id, statements)
                }
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Let(Identifier, ExprId),
    Ret(Option<ExprId>, RetMode),
    LetFn(Identifier, Vec<Annotation>, Vec<Parameter>, Return, ExprId),
    Struct(Identifier, Vec<Annotation>, Vec<Field>),
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

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub span: Span,
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
pub enum TypeDefKind {
    Simple(Vec<IdentRefId>),
    Array(TypeDefId, usize),
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExitPoint {
    Explicit(Option<ExprId>),
    Implicit(Option<ExprId>),
}

impl ExitPoint {
    pub fn expr_id(&self) -> Option<ExprId> {
        match self {
            ExitPoint::Explicit(e) | ExitPoint::Implicit(e) => *e,
        }
    }
}

#[derive(PartialEq, Default, Debug)]
pub struct ExitPoints {
    pub exit_points: IdMap<ExprId, Vec<ExitPoint>>,
    // todo:feature do something with it to actually shake the tree and remove the unreachable
    //   nodes. this potentially allows us to get rid of (or simplify a lot) the ExitPointResolver
    //   (it becomes a matter of extracting all the Ret's from the statements)
    pub unreachable: Vec<ExprId>,
}
