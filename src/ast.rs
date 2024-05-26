pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{Expression, ExpressionKind, Typed, TypedState, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{Bound, BoundState, IdentifierRef, Unbound};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Parameter, Statement, StatementKind};
use crate::desugar::ImplicitRet;
use crate::error::Diagnostics;
use crate::natives::Natives;
use crate::resolver::{Resolver, Symbol, Type};
use crate::vec_map::VecMap;
use std::collections::HashMap;
use std::marker::PhantomData;

pub type ResolvedAst = Ast<WithoutImplicitRet, Typed, Bound>;

#[derive(Debug, PartialEq)]
pub struct Ast<R, T, B>
where
    T: TypedState,
    B: BoundState,
{
    /// Unique identifiers names
    identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    identifier_refs: VecMap<IdentRefId, IdentifierRef<B>>,
    /// All expressions
    expressions: VecMap<ExprId, Expression<T>>,
    /// All statements
    statements: VecMap<StmtId, Statement<B>>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
    /// All symbols
    symbols: VecMap<SymbolId, Symbol>,
    /// All types
    types: VecMap<TypeId, Type>,
    implicit_ret: PhantomData<R>,
}

#[derive(Debug, PartialEq)]
pub struct WithImplicitRet {}

#[derive(Debug, PartialEq)]
pub struct WithoutImplicitRet {}

impl<R, T, B> Ast<R, T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn roots(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifiers(&self) -> &VecMap<IdentId, String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id]
    }

    pub fn root_statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    #[cfg(test)]
    pub fn identifier_ref_id(&self, start: usize) -> IdentRefId {
        for (id, ident_ref) in &self.identifier_refs {
            if ident_ref.ident().span().start() == start {
                return id;
            }
        }
        panic!("No identifier ref found at {}", start)
    }

    #[cfg(test)]
    pub fn expressions(&self) -> &VecMap<ExprId, Expression<T>> {
        &self.expressions
    }

    #[cfg(test)]
    pub fn statements(&self) -> &VecMap<StmtId, Statement<B>> {
        &self.statements
    }

    #[cfg(test)]
    pub fn expression_id(&self, start: usize) -> ExprId {
        for (id, expr) in &self.expressions {
            if expr.span().start() == start {
                return id;
            }
        }
        panic!("No expression found at {}", start)
    }

    #[cfg(test)]
    pub fn statement_id(&self, start: usize) -> StmtId {
        for (id, stmt) in &self.statements {
            if stmt.span().start() == start {
                return id;
            }
        }
        panic!("No statement found at {}", start)
    }
}

impl Ast<WithImplicitRet, Untyped, Unbound> {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef<Unbound>>,
        expressions: Vec<Expression<Untyped>>,
        statements: Vec<Statement<Unbound>>,
        root: Vec<StmtId>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs: identifier_refs.into(),
            expressions: expressions.into(),
            statements: statements.into(),
            root,
            symbols: Default::default(),
            types: Default::default(),
            implicit_ret: Default::default(),
        }
    }

    pub fn convert_implicit_ret(
        mut self,
        converter: ImplicitRet,
    ) -> Ast<WithoutImplicitRet, Untyped, Unbound> {
        for statement in converter.convert(&self) {
            self.statements.insert(statement.id(), statement);
        }
        Ast::<WithoutImplicitRet, Untyped, Unbound> {
            identifiers: self.identifiers,
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
            statements: self.statements,
            root: self.root,
            symbols: self.symbols,
            types: self.types,
            implicit_ret: Default::default(),
        }
    }
}

impl Ast<WithoutImplicitRet, Untyped, Unbound> {
    pub fn resolve(self, resolver: Resolver, natives: Natives) -> Result<ResolvedAst, Diagnostics> {
        let expressions_count = self.expressions.len();
        let statements_count = self.statements.len();

        let ast = self.merge(Into::<Ast<WithoutImplicitRet, Untyped, Unbound>>::into(
            &natives,
        ));

        resolver
            .resolve(
                ast.identifiers,
                ast.identifier_refs,
                ast.expressions,
                ast.statements,
                ast.root,
                natives,
            )
            .map(|r| {
                debug_assert!(
                    expressions_count == r.expressions.len(),
                    "expr count don't match ({} != {})",
                    expressions_count,
                    r.expressions.len()
                );
                debug_assert!(
                    statements_count == r.statements.len(),
                    "stmt count don't match ({} != {})",
                    statements_count,
                    r.statements.len()
                );

                Ast::<WithoutImplicitRet, Typed, Bound> {
                    identifiers: r.identifiers,
                    identifier_refs: r.identifier_refs,
                    expressions: r.expressions,
                    statements: r.statements,
                    root: r.root,
                    symbols: r.symbols,
                    types: r.types,
                    implicit_ret: PhantomData::<WithoutImplicitRet>,
                }
            })
    }

    fn merge(
        self,
        other: Ast<WithoutImplicitRet, Untyped, Unbound>,
    ) -> Ast<WithoutImplicitRet, Untyped, Unbound> {
        let mut identifiers = self.identifiers.into_reversed::<HashMap<_, _>>();

        // maps from old IdentId (i.e. from the "other" ast) to new IdentId
        let mut ident_map = HashMap::new();

        for (old_id, ident) in other.identifiers.into_iter() {
            let new_id = if let Some(id) = identifiers.get(&ident) {
                *id
            } else {
                let new_id = IdentId::from(identifiers.len());
                identifiers.insert(ident, new_id);
                new_id
            };
            ident_map.insert(old_id, new_id);
        }

        debug_assert!(!self.identifier_refs.has_holes());
        let mut identifier_refs = self.identifier_refs;

        // maps from old IdentRefId (i.e. from the "other" ast) to new IdentRefId
        let mut ident_ref_map = HashMap::new();

        // let mut ident_ref_map = Vec::with_capacity(other.identifier_refs.len());
        for (old_id, ident_ref) in other.identifier_refs.into_iter() {
            let new_id = identifier_refs.push(IdentifierRef::new(
                identifier_refs.next_index(),
                Identifier::new(
                    *ident_map
                        .get(&ident_ref.ident().id())
                        .expect("old->new mapping exists"),
                    ident_ref.ident().span().clone(),
                ),
            ));
            ident_ref_map.insert(old_id, new_id);
        }

        let stmt_base = self.statements.len();
        let expr_base = self.expressions.len();

        let mut expressions = self.expressions;
        for (id, expression) in other.expressions {
            let expression = Expression::new(
                id + expr_base,
                match expression.kind() {
                    ExpressionKind::Assignment(ident_ref, expr) => ExpressionKind::Assignment(
                        *ident_ref_map
                            .get(ident_ref)
                            .expect("old->new mapping exists"),
                        expr + expr_base,
                    ),
                    ExpressionKind::If(cond, true_branch, false_branch) => ExpressionKind::If(
                        cond + expr_base,
                        true_branch + expr_base,
                        false_branch.map(|expr| expr + expr_base),
                    ),
                    ExpressionKind::Literal(lit) => match lit.kind() {
                        LiteralKind::Boolean(b) => ExpressionKind::Literal(Literal::new(
                            LiteralKind::Boolean(*b),
                            lit.span().clone(),
                        )),
                        LiteralKind::Identifier(ident_ref) => {
                            ExpressionKind::Literal(Literal::new(
                                LiteralKind::Identifier(
                                    *ident_ref_map
                                        .get(ident_ref)
                                        .expect("old->new mapping exists"),
                                ),
                                lit.span().clone(),
                            ))
                        }
                        LiteralKind::Number(n) => ExpressionKind::Literal(Literal::new(
                            LiteralKind::Number(*n),
                            lit.span().clone(),
                        )),
                    },
                    ExpressionKind::Binary(left, op, right) => {
                        ExpressionKind::Binary(left + expr_base, op.clone(), right + expr_base)
                    }
                    ExpressionKind::FunctionCall(ident_ref, parameters) => {
                        ExpressionKind::FunctionCall(
                            *ident_ref_map
                                .get(ident_ref)
                                .expect("old->new mapping exists"),
                            parameters
                                .iter()
                                .map(|e| e + expr_base)
                                .collect::<Vec<ExprId>>(),
                        )
                    }
                    ExpressionKind::Unary(op, expr) => {
                        ExpressionKind::Unary(op.clone(), expr + expr_base)
                    }
                    ExpressionKind::While(cond, expr) => {
                        ExpressionKind::While(cond + expr_base, expr + expr_base)
                    }
                    ExpressionKind::Block(stmts) => ExpressionKind::Block(
                        stmts.iter().map(|s| s + stmt_base).collect::<Vec<StmtId>>(),
                    ),
                    ExpressionKind::Dummy => ExpressionKind::Dummy,
                },
                expression.span().clone(),
            );

            expressions.push(expression);
        }

        let mut statements = self.statements;

        for (id, statement) in other.statements {
            let span = statement.span().clone();
            let statement = Statement::new(
                id + stmt_base,
                match statement.take_kind() {
                    StatementKind::Expression(expr) => StatementKind::Expression(expr + expr_base),
                    StatementKind::Let(identifier, expr) => StatementKind::Let(
                        Identifier::new(
                            *ident_map
                                .get(&identifier.id())
                                .expect("old->new mapping exists"),
                            identifier.span().clone(),
                        ),
                        expr + expr_base,
                    ),
                    StatementKind::Ret(expr, mode) => StatementKind::Ret(expr + expr_base, mode),
                    StatementKind::LetFn(identifier, parameters, return_type, expr) => {
                        StatementKind::LetFn(
                            Identifier::new(
                                *ident_map
                                    .get(&identifier.id())
                                    .expect("old->new mapping exists"),
                                identifier.span().clone(),
                            ),
                            parameters
                                .iter()
                                .map(|p| {
                                    Parameter::new(
                                        Identifier::new(
                                            *ident_map
                                                .get(&p.identifier().id())
                                                .expect("old->new mapping exists"),
                                            p.identifier().span().clone(),
                                        ),
                                        Identifier::new(
                                            *ident_map
                                                .get(&p.ty().id())
                                                .expect("old->new mapping exists"),
                                            p.ty().span().clone(),
                                        ),
                                        p.span().clone(),
                                    )
                                })
                                .collect::<Vec<Parameter<Unbound>>>(),
                            return_type.map_identifier(|ident| {
                                Identifier::new(
                                    *ident_map.get(&ident.id()).expect("old->new mapping exists"),
                                    ident.span().clone(),
                                )
                            }),
                            expr + expr_base,
                        )
                    }
                },
                span,
            );

            statements.push(statement);
        }

        let mut root = self.root;
        for stmt in other.root {
            root.push(StmtId::from(stmt_base + stmt.id()));
        }

        let mut identifiers = identifiers.into_iter().collect::<Vec<(String, IdentId)>>();

        identifiers.sort_by(|(_, id1), (_, id2)| id1.cmp(id2));

        let identifiers = identifiers
            .into_iter()
            .map(|(ident, _)| ident)
            .collect::<Vec<String>>();

        Ast::<WithoutImplicitRet, Untyped, Unbound> {
            // todo remove into()?
            identifiers: identifiers.into(),
            identifier_refs,
            expressions,
            statements,
            root,
            symbols: self.symbols,
            types: self.types,
            implicit_ret: self.implicit_ret,
        }
    }
}

impl<R> Ast<R, Untyped, Unbound> {
    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Unbound> {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression<Untyped> {
        &self.expressions[id]
    }

    pub fn statement(&self, id: StmtId) -> &Statement<Unbound> {
        &self.statements[id]
    }
}

impl<R> Ast<R, Typed, Bound> {
    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Bound> {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression<Typed> {
        &self.expressions[id]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions[id].ty_id()]
    }

    pub fn statement(&self, id: StmtId) -> &Statement<Bound> {
        &self.statements[id]
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id]
    }

    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id]
    }
}

#[cfg(test)]
mod tests {
    use crate::desugar::ImplicitRet;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use insta::assert_debug_snapshot;

    #[test]
    fn merge_1() {
        let ast1 = Parser::new(Lexer::new(
            "let x_1 = 0; let f_1(p_1: number): boolean = { p_1 == 1; } f_1(x_1);",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        let ast2 = Parser::new(Lexer::new(
            "let x_2 = 0; let f_2(p_2: number): boolean = { p_2 == 2; } f_2(x_2);",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        assert_debug_snapshot!(&ast1.merge(ast2));
    }

    #[test]
    fn merge_2() {
        let ast1 = Parser::new(Lexer::new("let x_1 = 0; x_1 = -x_1 * 2;"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new());

        let ast2 = Parser::new(Lexer::new("let x_2 = 0; x_2 = -x_2 * 2;"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new());

        assert_debug_snapshot!(&ast1.merge(ast2));
    }

    #[test]
    fn merge_if() {
        let ast1 = Parser::new(Lexer::new(
            "let c_1 = true; let t_1 = 1; let f_1 = 0; if c_1 { t_1; } else { f_1; }",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        let ast2 = Parser::new(Lexer::new(
            "let c_2 = true; let t_2 = 1; let f_2 = 0; if c_2 { t_2; } else { f_2; }",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        assert_debug_snapshot!(&ast1.merge(ast2));
    }

    #[test]
    fn merge_while() {
        let ast1 = Parser::new(Lexer::new(
            "let c_1 = true; let w_1 = 1; while c_1 { w_1; }",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        let ast2 = Parser::new(Lexer::new(
            "let c_2 = false; let w_2 = 2; while c_2 { w_2; }",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        assert_debug_snapshot!(&ast1.merge(ast2));
    }
}
