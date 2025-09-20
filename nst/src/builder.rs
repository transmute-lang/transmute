use crate::nodes::{Nst, StatementKind};
use bimap::BiHashMap;
use std::borrow::Cow;
use transmute_ast::expression::Expression as AstExpression;
use transmute_ast::expression::ExpressionKind as AstExpressionKind;
use transmute_ast::identifier::Identifier;
use transmute_ast::identifier_ref::IdentifierRef;
use transmute_ast::literal::{Literal, LiteralKind};
use transmute_ast::statement::Statement as AstStatement;
use transmute_ast::statement::StatementKind as AstStatementKind;
use transmute_ast::statement::TypeDef as AstTypeDef;
use transmute_ast::statement::TypeDefKind as AstTypeDefKind;
use transmute_ast::statement::{Parameter, RetMode, Return};
use transmute_ast::Ast;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, InputId, StmtId, TypeDefId};
use transmute_core::vec_map::VecMap;

#[derive(Default, Debug)]
pub struct NstBuilder<'s> {
    /// Unique identifiers names
    pub identifiers: BiHashMap<Cow<'s, str>, IdentId>,
    /// Identifier refs
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    /// All expressions
    pub expressions: VecMap<ExprId, AstExpression>,
    /// All statements
    pub statements: VecMap<StmtId, AstStatement>,
    /// Types
    pub type_defs: VecMap<TypeDefId, AstTypeDef>,
    /// Root statement
    pub root: Option<StmtId>,
}

impl<'s> NstBuilder<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn number_literal(&mut self, number: i64) -> Literal {
        Literal {
            kind: LiteralKind::Number(number),
            span: Default::default(),
        }
    }

    pub fn string_literal<S>(&mut self, string: S) -> Literal
    where
        S: Into<String>,
    {
        Literal {
            kind: LiteralKind::String(string.into()),
            span: Default::default(),
        }
    }

    pub fn identifier_literal<I>(&mut self, ident_ref_id: I) -> Literal
    where
        I: ToIdentRefId<'s>,
    {
        Literal {
            kind: LiteralKind::Identifier(ident_ref_id.to_ident_ref_id(self)),
            span: Default::default(),
        }
    }

    pub fn push_identifier<'b, S>(&'b mut self, name: S) -> IdentId
    where
        S: Into<Cow<'s, str>>,
    {
        let name = name.into();
        match self.identifiers.get_by_left(&name) {
            None => {
                let ident_id = IdentId::from(self.identifiers.len());
                self.identifiers.insert(name, ident_id);
                ident_id
            }
            Some(ident_id) => *ident_id,
        }
    }

    pub fn push_identifier_ref<I>(&mut self, ident: I) -> IdentRefId
    where
        I: ToIdentId<'s>,
    {
        let ident = Identifier {
            id: ident.to_ident_id(self),
            span: Default::default(),
        };
        let id = self.identifier_refs.next_index();
        self.identifier_refs.push(IdentifierRef { id, ident })
    }

    pub fn push_type_def<S>(&mut self, name: S) -> TypeDefId
    where
        S: Into<Cow<'s, str>>,
    {
        let ident_id = self.push_identifier(name);
        let ident_ref_id = self.identifier_refs.next_index();
        self.identifier_refs.insert(
            ident_ref_id,
            IdentifierRef {
                id: ident_ref_id,
                ident: Identifier {
                    id: ident_id,
                    span: Default::default(),
                },
            },
        );
        let type_def = AstTypeDef {
            kind: AstTypeDefKind::Simple(vec![ident_ref_id]),
            span: Default::default(),
        };

        self.type_defs.push(type_def)
    }

    pub fn push_expression(&mut self, kind: AstExpressionKind) -> ExprId {
        let expr_id = self.expressions.next_index();
        self.expressions.push(AstExpression {
            id: expr_id,
            kind,
            span: Default::default(),
        })
    }

    pub fn push_statement(&mut self, kind: AstStatementKind) -> StmtId {
        let stmt_id = self.statements.next_index();
        self.statements.push(AstStatement {
            id: stmt_id,
            kind,
            span: Default::default(),
        })
    }

    // pub fn empty_block(&mut self) -> ExprId {
    //     self.push_expression(AstExpressionKind::Block(Vec::new()))
    // }

    pub fn append_statement<S: ToStmtId<'s>>(&mut self, e: S) -> StmtId {
        e.to_stmt_id(self)
    }

    pub fn set_root<S>(&mut self, root: S)
    where
        S: ToStmtId<'s> + 'static,
    {
        let stmt_id = root.to_stmt_id(self);
        self.root = Some(stmt_id);
    }
}

impl From<NstBuilder<'_>> for Nst {
    fn from(value: NstBuilder<'_>) -> Self {
        let mut ident_ids = value.identifiers.right_values().collect::<Vec<_>>();
        ident_ids.sort();
        let ast = Ast::new(
            ident_ids
                .into_iter()
                .map(|ident_id| {
                    value
                        .identifiers
                        .get_by_right(ident_id)
                        .expect("it exists")
                        .to_string()
                })
                .collect(),
            value.identifier_refs,
            value.expressions.values(),
            value.statements,
            value.root.expect("root statement exists"),
            value.type_defs,
        );

        Nst::from(ast)
    }
}

pub trait ToIdentId<'s> {
    fn to_ident_id(&self, builder: &mut NstBuilder<'s>) -> IdentId;
}

pub trait ToIdentRefId<'s> {
    fn to_ident_ref_id(&self, builder: &mut NstBuilder<'s>) -> IdentRefId;
}

pub trait ToTypeDefId<'s> {
    fn to_type_def_id(&self, builder: &mut NstBuilder<'s>) -> TypeDefId;
}

pub trait ToExprId<'s> {
    fn to_expr_id(&self, builder: &mut NstBuilder<'s>) -> ExprId;
}

pub trait ToStmtId<'s> {
    fn to_stmt_id(&self, builder: &mut NstBuilder<'s>) -> StmtId;
}

impl ToExprId<'_> for ExprId {
    fn to_expr_id(&self, _builder: &mut NstBuilder<'_>) -> ExprId {
        todo!()
    }
}

impl<'s> ToIdentId<'s> for IdentId {
    fn to_ident_id(&self, _builder: &mut NstBuilder<'s>) -> IdentId {
        *self
    }
}

impl<'s> ToIdentRefId<'s> for IdentId {
    fn to_ident_ref_id(&self, builder: &mut NstBuilder<'s>) -> IdentRefId {
        builder.push_identifier_ref(*self)
    }
}

impl ToExprId<'_> for IdentId {
    fn to_expr_id(&self, builder: &mut NstBuilder<'_>) -> ExprId {
        let literal = builder.identifier_literal(*self);
        builder.push_expression(AstExpressionKind::Literal(literal))
    }
}

impl<'s> ToTypeDefId<'s> for TypeDefId {
    fn to_type_def_id(&self, _builder: &mut NstBuilder<'s>) -> TypeDefId {
        *self
    }
}

impl ToExprId<'_> for () {
    fn to_expr_id(&self, builder: &mut NstBuilder<'_>) -> ExprId {
        builder.push_expression(AstExpressionKind::Block(vec![]))
    }
}

impl ToExprId<'_> for bool {
    fn to_expr_id(&self, builder: &mut NstBuilder<'_>) -> ExprId {
        builder.push_expression(AstExpressionKind::Literal(Literal {
            kind: LiteralKind::Boolean(*self),
            span: Default::default(),
        }))
    }
}

impl ToExprId<'_> for &str {
    fn to_expr_id(&self, builder: &mut NstBuilder<'_>) -> ExprId {
        let literal = builder.string_literal(*self);
        builder.push_expression(AstExpressionKind::Literal(literal))
    }
}

impl<'s> ToIdentId<'s> for &'s str {
    fn to_ident_id(&self, builder: &mut NstBuilder<'s>) -> IdentId {
        builder.push_identifier(*self)
    }
}

impl<'s> ToTypeDefId<'s> for &'s str {
    fn to_type_def_id(&self, builder: &mut NstBuilder<'s>) -> TypeDefId {
        builder.push_type_def(*self)
    }
}

impl ToExprId<'_> for i64 {
    fn to_expr_id(&self, builder: &mut NstBuilder<'_>) -> ExprId {
        let literal = builder.number_literal(*self);
        builder.push_expression(AstExpressionKind::Literal(literal))
    }
}

impl ToStmtId<'_> for StmtId {
    fn to_stmt_id(&self, _builder: &mut NstBuilder<'_>) -> StmtId {
        *self
    }
}

impl<'s, T> ToStmtId<'s> for T
where
    T: ToExprId<'s> + ?Sized,
{
    fn to_stmt_id(&self, builder: &mut NstBuilder<'s>) -> StmtId {
        let expr_id = self.to_expr_id(builder);
        builder.push_statement(AstStatementKind::Expression(expr_id))
    }
}

#[derive(Default)]
pub struct Block<'s> {
    stmt: Vec<Box<dyn ToStmtId<'s>>>,
}

impl<'s> Block<'s> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push<T>(&mut self, stmt: T)
    where
        T: ToStmtId<'s> + 'static,
    {
        self.stmt.push(Box::new(stmt));
    }
}

impl<'s> ToExprId<'s> for Block<'s> {
    fn to_expr_id(&self, builder: &mut NstBuilder<'s>) -> ExprId {
        let stmt_ids = self.stmt.iter().map(|st| st.to_stmt_id(builder)).collect();
        builder.push_expression(AstExpressionKind::Block(stmt_ids))
    }
}

pub struct If<'s> {
    cond: Box<dyn ToExprId<'s>>,
    true_expr: Box<dyn ToExprId<'s>>,
    false_expr: Option<Box<dyn ToExprId<'s>>>,
}

impl<'s> If<'s> {
    pub fn new<C, E>(cond: C, true_expr: E) -> Self
    where
        C: ToExprId<'s> + 'static,
        E: ToExprId<'s> + 'static,
    {
        Self {
            cond: Box::new(cond),
            true_expr: Box::new(true_expr),
            false_expr: None,
        }
    }

    pub fn with_false_expr<E>(&mut self, false_expr: E)
    where
        E: ToExprId<'s> + 'static,
    {
        self.false_expr = Some(Box::new(false_expr));
    }
}

impl<'s> ToExprId<'s> for If<'s> {
    fn to_expr_id(&self, builder: &mut NstBuilder<'s>) -> ExprId {
        let cond = self.cond.to_expr_id(builder);
        let true_expr = self.true_expr.to_expr_id(builder);
        let false_expr = self.false_expr.as_ref().map(|e| e.to_expr_id(builder));
        builder.push_expression(AstExpressionKind::If(cond, true_expr, false_expr))
    }
}

pub struct FnCall<'s> {
    expr_id: Box<dyn ToExprId<'s>>,
    parameters: Vec<Box<dyn ToExprId<'s>>>,
}

impl<'s> FnCall<'s> {
    pub fn new<I>(expr: I) -> Self
    where
        I: ToExprId<'s> + 'static,
    {
        Self {
            expr_id: Box::new(expr),
            parameters: vec![],
        }
    }

    pub fn with_parameter<P>(mut self, parameters: P) -> Self
    where
        P: ToExprId<'s> + 'static,
    {
        self.parameters.push(Box::new(parameters));
        self
    }
}

impl<'s> ToExprId<'s> for FnCall<'s> {
    fn to_expr_id(&self, builder: &mut NstBuilder<'s>) -> ExprId {
        let expr_id = self.expr_id.to_expr_id(builder);
        let parameters = self
            .parameters
            .iter()
            .map(|p| p.to_expr_id(builder))
            .collect();
        builder.push_expression(AstExpressionKind::FunctionCall(expr_id, parameters))
    }
}

pub struct Namespace<'s> {
    name: Box<dyn ToIdentId<'s>>,
    statements: Vec<Box<dyn ToStmtId<'s>>>,
}

impl<'s> Namespace<'s> {
    pub fn new<I>(name: I) -> Self
    where
        I: ToIdentId<'s> + 'static,
    {
        Self {
            name: Box::new(name),
            statements: Default::default(),
        }
    }

    pub fn push<S>(&mut self, stmt: S)
    where
        S: ToStmtId<'s> + 'static,
    {
        self.statements.push(Box::new(stmt));
    }
}

impl<'s> ToStmtId<'s> for Namespace<'s> {
    fn to_stmt_id(&self, builder: &mut NstBuilder<'s>) -> StmtId {
        let id = self.name.to_ident_id(builder);
        let statements = self
            .statements
            .iter()
            .map(|s| s.to_stmt_id(builder))
            .collect();
        builder.push_statement(AstStatementKind::Namespace(
            Identifier {
                id,
                span: Default::default(),
            },
            InputId::default(),
            statements,
        ))
    }
}

pub struct Function<'s> {
    name: Box<dyn ToIdentId<'s>>,
    parameters: Vec<(Box<dyn ToIdentId<'s>>, Box<dyn ToTypeDefId<'s>>)>,
    return_type: Option<TypeDefId>,
    body: Option<Box<dyn ToExprId<'s>>>,
}

impl<'s> Function<'s> {
    pub fn new<I>(name: I) -> Self
    where
        I: ToIdentId<'s> + 'static,
    {
        Self {
            name: Box::new(name),
            parameters: Vec::new(),
            return_type: None,
            body: None,
        }
    }

    pub fn add_parameter<I, T>(&mut self, name: I, type_def_id: T)
    where
        I: ToIdentId<'s> + 'static,
        T: ToTypeDefId<'s> + 'static,
    {
        self.parameters
            .push((Box::new(name), Box::new(type_def_id)));
    }

    pub fn with_ret_type(&mut self, type_def_id: TypeDefId) {
        self.return_type = Some(type_def_id);
    }

    pub fn with_body<E>(&mut self, body: E)
    where
        E: ToExprId<'s> + 'static,
    {
        self.body = Some(Box::new(body))
    }
}

pub struct Ret<'s> {
    expr: Box<dyn ToExprId<'s>>,
}

impl<'s> Ret<'s> {
    pub fn new<E>(expr: E) -> Self
    where
        E: ToExprId<'s> + 'static,
    {
        Self {
            expr: Box::new(expr),
        }
    }
}

impl<'s> ToStmtId<'s> for Ret<'s> {
    fn to_stmt_id(&self, builder: &mut NstBuilder<'s>) -> StmtId {
        let expr = self.expr.to_expr_id(builder);
        builder.push_statement(AstStatementKind::Ret(Some(expr), RetMode::Explicit))
    }
}

impl<'s> ToStmtId<'s> for Function<'s> {
    fn to_stmt_id(&self, builder: &mut NstBuilder<'s>) -> StmtId {
        let body = self
            .body
            .as_ref()
            .map(|e| e.as_ref().to_expr_id(builder))
            .unwrap_or_else(|| ().to_expr_id(builder));

        let ident_id = self.name.to_ident_id(builder);

        let parameters = self
            .parameters
            .iter()
            .map(|(id, type_def_id)| Parameter {
                identifier: Identifier {
                    id: id.to_ident_id(builder),
                    span: Default::default(),
                },
                type_def_id: type_def_id.to_type_def_id(builder),
                span: Default::default(),
            })
            .collect();

        builder.push_statement(AstStatementKind::LetFn(
            Identifier {
                id: ident_id,
                span: Default::default(),
            },
            Vec::new(),
            parameters,
            Return {
                type_def_id: self.return_type,
            },
            body,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pretty_print::Options;
    use insta::{assert_debug_snapshot, assert_snapshot};

    #[test]
    fn fibonacci() {
        let mut builder = NstBuilder::new();

        let mut root_ns = Namespace::new("<root>");
        let mut core_ns = Namespace::new("core");

        let number = builder.push_type_def("number");

        let mut function = Function::new("f");
        let n = "n".to_ident_id(&mut builder);
        function.add_parameter(n, number);
        function.with_ret_type(number);

        let mut block = Block::new();

        let mut ret_block = Block::new();
        ret_block.push(Ret::new(n));

        block.push(If::new(
            FnCall::new("lt".to_ident_id(&mut builder))
                .with_parameter(n)
                .with_parameter(2),
            ret_block,
        ));

        block.push(
            FnCall::new("plus".to_ident_id(&mut builder))
                .with_parameter(
                    FnCall::new("f".to_ident_id(&mut builder)).with_parameter(
                        FnCall::new("minus".to_ident_id(&mut builder))
                            .with_parameter(n)
                            .with_parameter(1),
                    ),
                )
                .with_parameter(
                    FnCall::new("f".to_ident_id(&mut builder)).with_parameter(
                        FnCall::new("minus".to_ident_id(&mut builder))
                            .with_parameter(n)
                            .with_parameter(2),
                    ),
                ),
        );

        function.with_body(block);

        core_ns.push(function);
        root_ns.push(core_ns);

        let stmt_id = builder.append_statement(root_ns);
        builder.set_root(stmt_id);
        let something = Into::<Nst>::into(builder);

        assert_debug_snapshot!(something);
    }
}
