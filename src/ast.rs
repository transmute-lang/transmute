pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::Unresolved;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Parameter, Statement, StatementKind};
use crate::desugar::ImplicitRet;
use crate::error::Diagnostics;
use crate::natives::Natives;
use crate::resolver::{Resolver, Symbol, Type, TypeId};
use crate::vec_map::VecMap;
use identifier_ref::{IdentifierRef, Resolved};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub struct Ast<S> {
    /// Unique identifiers names
    identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    identifier_refs: VecMap<IdentRefId, IdentifierRef<Unresolved>>,
    /// All expressions
    expressions: VecMap<ExprId, Expression>,
    /// All statements
    statements: VecMap<StmtId, Statement>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
    implicit_ret: PhantomData<S>,
}

#[derive(Debug, PartialEq)]
pub struct WithImplicitRet {}

#[derive(Debug, PartialEq)]
pub struct WithoutImplicitRet {}

impl Ast<WithImplicitRet> {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef<Unresolved>>,
        expressions: Vec<Expression>,
        statements: Vec<Statement>,
        root: Vec<StmtId>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs: identifier_refs.into(),
            expressions: expressions.into(),
            statements: statements.into(),
            root,
            implicit_ret: Default::default(),
        }
    }

    pub fn convert_implicit_ret(mut self, converter: ImplicitRet) -> Ast<WithoutImplicitRet> {
        let statements = converter.convert(&self);
        for statement in statements {
            self.replace_statement(statement);
        }
        Ast::<WithoutImplicitRet> {
            identifiers: self.identifiers,
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
            statements: self.statements,
            root: self.root,
            implicit_ret: Default::default(),
        }
    }
}

impl Ast<WithoutImplicitRet> {
    pub fn resolve(self, resolver: Resolver, natives: Natives) -> Result<ResolvedAst, Diagnostics> {
        let ast = self.merge(Into::<Ast<WithoutImplicitRet>>::into(&natives));
        resolver.resolve(&ast, natives).map(|r| {
            let mut ast = ast;
            for (_id, expression) in r.expressions.into_iter() {
                ast.replace_expression(expression);
            }
            // todo remove the into()'s
            ResolvedAst {
                identifiers: ast.identifiers,
                identifier_refs: r.identifier_refs,
                expressions: ast.expressions,
                statements: ast.statements,
                root: ast.root,
                symbols: r.symbols,
                types: r.types,
                expressions_types: r.expression_types,
            }
        })
    }

    fn merge(self, other: Ast<WithoutImplicitRet>) -> Ast<WithoutImplicitRet> {
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
            let statement = Statement::new(
                id + stmt_base,
                match statement.kind() {
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
                    StatementKind::Ret(expr, mode) => StatementKind::Ret(expr + expr_base, *mode),
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
                                .collect::<Vec<Parameter>>(),
                            return_type.as_ref().map(|t| {
                                Identifier::new(
                                    *ident_map.get(&t.id()).expect("old->new mapping exists"),
                                    t.span().clone(),
                                )
                            }),
                            expr + expr_base,
                        )
                    }
                },
                statement.span().clone(),
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

        Ast::<WithoutImplicitRet> {
            // todo remove into()?
            identifiers: identifiers.into(),
            identifier_refs,
            expressions,
            statements,
            root,
            implicit_ret: Default::default(),
        }
    }
}

impl<S> Ast<S> {
    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id]
    }

    pub fn identifier_id(&self, name: &str) -> IdentId {
        // todo use a map instead
        for (id, ident) in self.identifiers.iter() {
            if ident == name {
                return id;
            }
        }
        panic!("Identifier {} not found", name)
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Unresolved> {
        &self.identifier_refs[id]
    }

    pub fn identifier_ref_count(&self) -> usize {
        self.identifier_refs.len()
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

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id]
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

    pub fn expressions_count(&self) -> usize {
        self.expressions.len()
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id]
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

    fn replace_expression(&mut self, expression: Expression) {
        self.expressions.insert(expression.id(), expression);
    }

    fn replace_statement(&mut self, statement: Statement) {
        self.statements.insert(statement.id(), statement);
    }
}

#[derive(Debug)]
pub struct ResolvedAst {
    /// Unique identifiers names
    identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    identifier_refs: VecMap<IdentRefId, IdentifierRef<Resolved>>,
    /// All expressions
    expressions: VecMap<ExprId, Expression>,
    /// All statements
    statements: VecMap<StmtId, Statement>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
    /// All symbols
    symbols: VecMap<SymbolId, Symbol>,
    /// All types
    types: VecMap<TypeId, Type>,
    /// Types of all expressions
    expressions_types: VecMap<ExprId, TypeId>,
}

impl ResolvedAst {
    pub fn identifiers(&self) -> &VecMap<IdentId, String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id]
    }

    pub fn identifier_id(&self, name: &str) -> IdentId {
        // todo use a map instead
        for (id, ident) in self.identifiers.iter() {
            if ident == name {
                return id;
            }
        }
        panic!("Identifier {} not found", name)
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Resolved> {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions_types[id]]
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id]
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id]
    }

    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id]
    }
}

pub struct AstNodePrettyPrint<'a, S, T> {
    indent: usize,
    ast: Rc<AstKind<'a, S>>,
    id: T,
}

// todo maybe a trait instead of an enum and manual dispatch....
enum AstKind<'a, S> {
    Unresolved(&'a Ast<S>),
    Resolved(&'a ResolvedAst),
}

impl<'a, S> AstKind<'a, S> {
    fn identifier(&self, id: IdentId) -> &str {
        match self {
            AstKind::Unresolved(a) => &a.identifiers[id],
            AstKind::Resolved(a) => &a.identifiers[id],
        }
    }

    fn identifier_ref(&self, id: IdentRefId) -> IdentifierRef<Unresolved> {
        match self {
            AstKind::Unresolved(a) => a.identifier_refs[id].clone(),
            AstKind::Resolved(a) => {
                let ident_ref = &a.identifier_refs[id];
                IdentifierRef::new(ident_ref.id(), ident_ref.ident().clone())
            }
        }
    }

    fn expression(&self, id: ExprId) -> &Expression {
        match self {
            AstKind::Unresolved(a) => &a.expressions[id],
            AstKind::Resolved(a) => &a.expressions[id],
        }
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        match self {
            AstKind::Unresolved(a) => &a.statements[id],
            AstKind::Resolved(a) => &a.statements[id],
        }
    }
}

impl<'a, S> AstNodePrettyPrint<'a, S, StmtId> {
    pub fn new_unresolved(ast: &'a Ast<S>) -> Self {
        Self {
            indent: 0,
            ast: Rc::new(AstKind::Unresolved(ast)),
            id: *ast.statements().first().unwrap(),
        }
    }

    pub fn new_resolved(ast: &'a ResolvedAst) -> Self {
        Self {
            indent: 0,
            ast: Rc::new(AstKind::Resolved(ast)),
            id: *ast.statements().first().unwrap(),
        }
    }
}

impl<'a, S, T> AstNodePrettyPrint<'a, S, T> {
    fn new_with_ident(ast: Rc<AstKind<'a, S>>, id: T, ident: usize) -> Self {
        Self {
            indent: ident,
            ast,
            id,
        }
    }
}

impl<S> Display for AstNodePrettyPrint<'_, S, StmtId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.statement(self.id).kind() {
            StatementKind::Expression(expr) => {
                let semi = match self.ast.expression(*expr).kind() {
                    ExpressionKind::If(_, _, _) | ExpressionKind::While(_, _) => "",
                    _ => ";",
                };
                writeln!(
                    f,
                    "{indent}{}{semi}",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent)
                )
            }
            StatementKind::Let(ident, expr) => {
                writeln!(
                    f,
                    "{indent}let {} = {};",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), ident.id(), 0),
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent),
                )
            }
            StatementKind::Ret(expr, _) => {
                writeln!(
                    f,
                    "{indent}ret {};",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent)
                )
            }
            StatementKind::LetFn(ident, params, ty, expr) => {
                write!(
                    f,
                    "{indent}let {}(",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), ident.id(), 0)
                )?;
                for (i, param) in params.iter().enumerate() {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            param.identifier().id(),
                            0
                        )
                    )?;
                    write!(f, ": ")?;
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), param.ty().id(), 0)
                    )?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                let ty = ty
                    .as_ref()
                    .map(|ty| {
                        format!(
                            ": {}",
                            AstNodePrettyPrint::new_with_ident(self.ast.clone(), ty.id(), 0)
                        )
                    })
                    .unwrap_or_default();

                writeln!(f, "){ty} = {{",)?;

                let stmts = match self.ast.expression(*expr).kind() {
                    ExpressionKind::Block(stmts) => stmts,
                    _ => panic!("block expected"),
                };

                for stmt in stmts {
                    write!(
                        f,
                        "{indent}{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            *stmt,
                            self.indent + 1
                        )
                    )?;
                }
                writeln!(f, "{indent}}}")
            }
        }
    }
}

impl<S> Display for AstNodePrettyPrint<'_, S, ExprId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.expression(self.id).kind() {
            ExpressionKind::Assignment(ident, expr) => {
                write!(
                    f,
                    "{} = {}",
                    AstNodePrettyPrint::new_with_ident(
                        self.ast.clone(),
                        self.ast.identifier_ref(*ident).ident().id(),
                        0
                    ),
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, 0)
                )
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                writeln!(
                    f,
                    "if {} {{",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *cond, 0)
                )?;

                let true_branch = match self.ast.expression(*true_branch).kind() {
                    ExpressionKind::Block(true_branch) => true_branch,
                    _ => panic!("block expected"),
                };

                for stmt in true_branch {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            *stmt,
                            self.indent + 1
                        )
                    )?;
                }
                if let Some(false_branch) = false_branch {
                    writeln!(f, "{indent}}}")?;
                    writeln!(f, "{indent}else {{")?;

                    let false_branch = match self.ast.expression(*false_branch).kind() {
                        ExpressionKind::Block(true_branch) => true_branch,
                        _ => panic!("block expected"),
                    };

                    for stmt in false_branch {
                        write!(
                            f,
                            "{}",
                            AstNodePrettyPrint::new_with_ident(
                                self.ast.clone(),
                                *stmt,
                                self.indent + 1
                            )
                        )?;
                    }
                }
                write!(f, "{indent}}}")
            }
            ExpressionKind::Literal(lit) => match lit.kind() {
                LiteralKind::Boolean(b) => write!(f, "{b}"),
                LiteralKind::Identifier(ident) => {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            self.ast.identifier_ref(*ident).ident().id(),
                            0
                        )
                    )
                }
                LiteralKind::Number(n) => write!(f, "{n}"),
            },
            ExpressionKind::Binary(left, op, right) => {
                write!(
                    f,
                    "{} {} {}",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *left, 0),
                    op.kind(),
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *right, 0)
                )
            }
            ExpressionKind::FunctionCall(ident, params) => {
                write!(
                    f,
                    "{}(",
                    AstNodePrettyPrint::new_with_ident(
                        self.ast.clone(),
                        self.ast.identifier_ref(*ident).ident().id(),
                        0
                    )
                )?;
                for (i, expr) in params.iter().enumerate() {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, 0)
                    )?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ExpressionKind::Unary(op, expr) => {
                write!(
                    f,
                    "{} {}",
                    op.kind(),
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, 0)
                )
            }
            ExpressionKind::While(cond, expr) => {
                writeln!(
                    f,
                    "while {} {{",
                    AstNodePrettyPrint::new_with_ident(self.ast.clone(), *cond, 0)
                )?;

                let stmts = match self.ast.expression(*expr).kind() {
                    ExpressionKind::Block(stmts) => stmts,
                    _ => panic!("block expected"),
                };

                for stmt in stmts {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            *stmt,
                            self.indent + 1
                        )
                    )?;
                }
                writeln!(f, "{indent}}}")
            }
            ExpressionKind::Block(stmts) => {
                writeln!(f, "{{")?;

                for stmt in stmts {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(
                            self.ast.clone(),
                            *stmt,
                            self.indent + 1
                        )
                    )?;
                }

                writeln!(f, "{indent}}}")
            }
            ExpressionKind::Dummy => {
                write!(f, "<<missing expression>>",)
            }
        }
    }
}

impl<S> Display for AstNodePrettyPrint<'_, S, IdentId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        write!(f, "{indent}{}", self.ast.identifier(self.id))
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::ids::StmtId;
    use crate::ast::{AstNodePrettyPrint, WithoutImplicitRet};
    use crate::desugar::ImplicitRet;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use insta::{assert_debug_snapshot, assert_snapshot};

    #[test]
    fn pretty_print() {
        let ast = Parser::new(Lexer::new(
            r#"
        let fact(n: number): number = {
            if n < 0 {
                let r = if false {
                    1;
                } else {
                    0;
                };
                ret r;
            } else {
                let product = 1;
                while n > 0 {
                    product = product * n;
                    n = n - 1;
                }
                product;
            }
        }
    "#,
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRet::new());

        let actual = format!(
            "{}",
            AstNodePrettyPrint::<WithoutImplicitRet, StmtId>::new_unresolved(&ast)
        );

        assert_snapshot!(actual);
    }

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
