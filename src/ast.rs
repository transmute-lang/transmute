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
use identifier_ref::{IdentifierRef, Resolved};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub struct Ast<S> {
    /// Unique identifiers names
    identifiers: Vec<String>,
    /// Identifier refs
    identifier_refs: Vec<IdentifierRef<Unresolved>>,
    /// All expressions
    expressions: Vec<Expression>,
    /// All statements
    statements: Vec<Statement>,
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
            identifiers,
            identifier_refs,
            expressions,
            statements,
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
            for expression in r.expressions.into_iter() {
                ast.replace_expression(expression);
            }
            // todo resolved ast use dedicated structs/enums to avoid tons of lookup
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
        let mut identifiers = self
            .identifiers
            .into_iter()
            .enumerate()
            .map(|(i, ident)| (ident, i))
            .collect::<HashMap<String, usize>>();

        let mut ident_map = Vec::with_capacity(other.identifiers.len());
        for ident in other.identifiers.into_iter() {
            if let Some(id) = identifiers.get(&ident) {
                ident_map.push(*id);
            } else {
                let id = identifiers.len();
                identifiers.insert(ident, id);
                ident_map.push(id);
            }
        }

        let mut identifier_refs = self.identifier_refs;
        let mut ident_ref_map = Vec::with_capacity(other.identifier_refs.len());
        for ident_ref in other.identifier_refs.into_iter() {
            let id = identifier_refs.len();
            identifier_refs.push(IdentifierRef::new(
                IdentRefId::from(id),
                Identifier::new(
                    IdentId::from(ident_map[ident_ref.ident().id().id()]),
                    ident_ref.ident().span().clone(),
                ),
            ));
            ident_ref_map.push(id);
        }

        let stmt_base = self.statements.len();
        let expr_base = self.expressions.len();

        let mut expressions = self.expressions;
        for expression in other.expressions {
            let expression = Expression::new(
                ExprId::from(expr_base + expression.id().id()),
                match expression.kind() {
                    ExpressionKind::Assignment(ident_ref, expr) => ExpressionKind::Assignment(
                        IdentRefId::from(ident_ref_map[ident_ref.id()]),
                        ExprId::from(expr_base + expr.id()),
                    ),
                    ExpressionKind::If(cond, true_branch, false_branch) => ExpressionKind::If(
                        ExprId::from(expr_base + cond.id()),
                        ExprId::from(expr_base + true_branch.id()),
                        false_branch.map(|expr| ExprId::from(expr_base + expr.id())),
                    ),
                    ExpressionKind::Literal(lit) => match lit.kind() {
                        LiteralKind::Boolean(b) => ExpressionKind::Literal(Literal::new(
                            LiteralKind::Boolean(*b),
                            lit.span().clone(),
                        )),
                        LiteralKind::Identifier(ident_ref) => {
                            ExpressionKind::Literal(Literal::new(
                                LiteralKind::Identifier(IdentRefId::from(
                                    ident_ref_map[ident_ref.id()],
                                )),
                                lit.span().clone(),
                            ))
                        }
                        LiteralKind::Number(n) => ExpressionKind::Literal(Literal::new(
                            LiteralKind::Number(*n),
                            lit.span().clone(),
                        )),
                    },
                    ExpressionKind::Binary(left, op, right) => ExpressionKind::Binary(
                        ExprId::from(expr_base + left.id()),
                        op.clone(),
                        ExprId::from(expr_base + right.id()),
                    ),
                    ExpressionKind::FunctionCall(ident_ref, parameters) => {
                        ExpressionKind::FunctionCall(
                            IdentRefId::from(ident_ref_map[ident_ref.id()]),
                            parameters
                                .iter()
                                .map(|e| ExprId::from(expr_base + e.id()))
                                .collect::<Vec<ExprId>>(),
                        )
                    }
                    ExpressionKind::Unary(op, expr) => {
                        ExpressionKind::Unary(op.clone(), ExprId::from(expr_base + expr.id()))
                    }
                    ExpressionKind::While(cond, expr) => ExpressionKind::While(
                        ExprId::from(expr_base + cond.id()),
                        ExprId::from(expr_base + expr.id()),
                    ),
                    ExpressionKind::Block(stmts) => ExpressionKind::Block(
                        stmts
                            .iter()
                            .map(|s| StmtId::from(stmt_base + s.id()))
                            .collect::<Vec<StmtId>>(),
                    ),
                    ExpressionKind::Dummy => ExpressionKind::Dummy,
                },
                expression.span().clone(),
            );

            expressions.push(expression);
        }

        let mut statements = self.statements;

        for statement in other.statements {
            let statement = Statement::new(
                StmtId::from(stmt_base + statement.id().id()),
                match statement.kind() {
                    StatementKind::Expression(expr) => {
                        StatementKind::Expression(ExprId::from(expr_base + expr.id()))
                    }
                    StatementKind::Let(identifier, expr) => StatementKind::Let(
                        Identifier::new(
                            IdentId::from(ident_map[identifier.id().id()]),
                            identifier.span().clone(),
                        ),
                        ExprId::from(expr_base + expr.id()),
                    ),
                    StatementKind::Ret(expr, mode) => {
                        StatementKind::Ret(ExprId::from(expr_base + expr.id()), *mode)
                    }
                    StatementKind::LetFn(identifier, parameters, return_type, expr) => {
                        StatementKind::LetFn(
                            Identifier::new(
                                IdentId::from(ident_map[identifier.id().id()]),
                                identifier.span().clone(),
                            ),
                            parameters
                                .iter()
                                .map(|p| {
                                    Parameter::new(
                                        Identifier::new(
                                            IdentId::from(ident_map[p.identifier().id().id()]),
                                            p.identifier().span().clone(),
                                        ),
                                        Identifier::new(
                                            IdentId::from(ident_map[p.ty().id().id()]),
                                            p.ty().span().clone(),
                                        ),
                                        p.span().clone(),
                                    )
                                })
                                .collect::<Vec<Parameter>>(),
                            return_type.as_ref().map(|t| {
                                Identifier::new(
                                    IdentId::from(ident_map[t.id().id()]),
                                    t.span().clone(),
                                )
                            }),
                            ExprId::from(expr_base + expr.id()),
                        )
                    }
                    StatementKind::Struct(_, _) => {
                        todo!()
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

        let mut identifiers = identifiers.into_iter().collect::<Vec<(String, usize)>>();

        identifiers.sort_by(|(_, id1), (_, id2)| id1.cmp(id2));

        let identifiers = identifiers
            .into_iter()
            .map(|(ident, _)| ident)
            .collect::<Vec<String>>();

        Ast::<WithoutImplicitRet> {
            identifiers,
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

    pub fn identifiers(&self) -> &Vec<String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id.id()]
    }

    pub fn identifier_id(&self, name: &str) -> IdentId {
        // todo use a map instead
        for (id, ident) in self.identifiers.iter().enumerate() {
            if ident == name {
                return IdentId::from(id);
            }
        }
        panic!("Identifier {} not found", name)
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Unresolved> {
        &self.identifier_refs[id.id()]
    }

    pub fn identifier_ref_count(&self) -> usize {
        self.identifier_refs.len()
    }

    #[cfg(test)]
    pub fn identifier_ref_id(&self, start: usize) -> IdentRefId {
        for ident_ref in &self.identifier_refs {
            if ident_ref.ident().span().start() == start {
                return ident_ref.id();
            }
        }
        panic!("No identifier ref found at {}", start)
    }

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id.id()]
    }

    #[cfg(test)]
    pub fn expression_id(&self, start: usize) -> ExprId {
        for expr in &self.expressions {
            if expr.span().start() == start {
                return expr.id();
            }
        }
        panic!("No expression found at {}", start)
    }

    pub fn expressions_count(&self) -> usize {
        self.expressions.len()
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id.id()]
    }

    #[cfg(test)]
    pub fn statement_id(&self, start: usize) -> StmtId {
        for stmt in &self.statements {
            if stmt.span().start() == start {
                return stmt.id();
            }
        }
        panic!("No statement found at {}", start)
    }

    fn replace_expression(&mut self, expression: Expression) {
        let id = expression.id().id();
        self.expressions[id] = expression
    }

    fn replace_statement(&mut self, statement: Statement) {
        let id = statement.id().id();
        self.statements[id] = statement
    }
}

#[derive(Debug)]
pub struct ResolvedAst {
    /// Unique identifiers names
    identifiers: Vec<String>,
    /// Identifier refs
    identifier_refs: Vec<IdentifierRef<Resolved>>,
    /// All expressions
    expressions: Vec<Expression>,
    /// All statements
    statements: Vec<Statement>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
    /// All symbols
    symbols: Vec<Symbol>,
    /// All types
    types: Vec<Type>,
    /// Types of all expressions
    expressions_types: Vec<TypeId>,
}

impl ResolvedAst {
    pub fn identifiers(&self) -> &Vec<String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id.id()]
    }

    pub fn identifier_id(&self, name: &str) -> IdentId {
        // todo use a map instead
        for (id, ident) in self.identifiers.iter().enumerate() {
            if ident == name {
                return IdentId::from(id);
            }
        }
        panic!("Identifier {} not found", name)
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Resolved> {
        &self.identifier_refs[id.id()]
    }

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id.id()]
    }

    pub fn expression_type(&self, id: ExprId) -> TypeId {
        self.expressions_types[id.id()]
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id.id()]
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.id()]
    }

    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id.id()]
    }

    pub fn x(&self) -> &Type {
        todo!()
    }
}

pub struct AstNodePrettyPrint<'a, S, T> {
    indent: usize,
    ast: Rc<AstKind<'a, S>>,
    id: Option<T>,
}

// todo maybe a trait instead of an enum and manual dispatch....
enum AstKind<'a, S> {
    Unresolved(&'a Ast<S>),
    Resolved(&'a ResolvedAst),
}

impl<'a, S> AstKind<'a, S> {
    fn identifier(&self, id: IdentId) -> &str {
        match self {
            AstKind::Unresolved(a) => &a.identifiers[id.id()],
            AstKind::Resolved(a) => &a.identifiers[id.id()],
        }
    }

    fn identifier_ref(&self, id: IdentRefId) -> IdentifierRef<Unresolved> {
        match self {
            AstKind::Unresolved(a) => a.identifier_refs[id.id()].clone(),
            AstKind::Resolved(a) => {
                let ident_ref = &a.identifier_refs[id.id()];
                IdentifierRef::new(ident_ref.id(), ident_ref.ident().clone())
            }
        }
    }

    fn expression(&self, id: ExprId) -> &Expression {
        match self {
            AstKind::Unresolved(a) => &a.expressions[id.id()],
            AstKind::Resolved(a) => &a.expressions[id.id()],
        }
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        match self {
            AstKind::Unresolved(a) => &a.statements[id.id()],
            AstKind::Resolved(a) => &a.statements[id.id()],
        }
    }
}

impl<'a, S> AstNodePrettyPrint<'a, S, StmtId> {
    pub fn new_unresolved(ast: &'a Ast<S>) -> Self {
        Self {
            indent: 0,
            ast: Rc::new(AstKind::Unresolved(ast)),
            id: None,
        }
    }

    pub fn new_resolved(ast: &'a ResolvedAst) -> Self {
        Self {
            indent: 0,
            ast: Rc::new(AstKind::Resolved(ast)),
            id: None,
        }
    }
}

impl<'a, S, T> AstNodePrettyPrint<'a, S, T> {
    fn new_with_ident(ast: Rc<AstKind<'a, S>>, id: T, ident: usize) -> Self {
        Self {
            indent: ident,
            ast,
            id: Some(id),
        }
    }
}

impl<S> Display for AstNodePrettyPrint<'_, S, StmtId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);

        let iter: Box<dyn Iterator<Item = &StmtId>> = match &self.id {
            None => match *self.ast.as_ref() {
                AstKind::Unresolved(ast) => Box::new(ast.statements().iter()),
                AstKind::Resolved(ast) => Box::new(ast.statements().iter()),
            },
            Some(_) => Box::new(self.id.iter()),
        };

        for stmt in iter {
            match self.ast.statement(*stmt).kind() {
                StatementKind::Expression(expr) => {
                    let semi = match self.ast.expression(*expr).kind() {
                        ExpressionKind::If(_, _, _) | ExpressionKind::While(_, _) => "",
                        _ => ";",
                    };
                    writeln!(
                        f,
                        "{indent}{}{semi}",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent)
                    )?;
                }
                StatementKind::Let(ident, expr) => {
                    writeln!(
                        f,
                        "{indent}let {} = {};",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), ident.id(), 0),
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent),
                    )?;
                }
                StatementKind::Ret(expr, _) => {
                    writeln!(
                        f,
                        "{indent}ret {};",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), *expr, self.indent)
                    )?;
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
                            "{name}: {ty}",
                            name = AstNodePrettyPrint::new_with_ident(
                                self.ast.clone(),
                                param.identifier().id(),
                                0
                            ),
                            ty = AstNodePrettyPrint::new_with_ident(
                                self.ast.clone(),
                                param.ty().id(),
                                0
                            )
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
                    writeln!(f, "{indent}}}")?;
                }
                StatementKind::Struct(ident, fields) => {
                    writeln!(
                        f,
                        "{indent}struct {} {{",
                        AstNodePrettyPrint::new_with_ident(self.ast.clone(), ident.id(), 0)
                    )?;

                    for field in fields.iter() {
                        writeln!(
                            f,
                            "{indent}  {name}: {ty},",
                            name = AstNodePrettyPrint::new_with_ident(
                                self.ast.clone(),
                                field.identifier().id(),
                                0
                            ),
                            ty = AstNodePrettyPrint::new_with_ident(
                                self.ast.clone(),
                                field.ty().id(),
                                0
                            )
                        )?;
                    }

                    writeln!(f, "{indent}}}")?;
                }
            }
        }
        Ok(())
    }
}

impl<S> Display for AstNodePrettyPrint<'_, S, ExprId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.expression(self.id.expect("ExprId exists")).kind() {
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
        write!(
            f,
            "{indent}{}",
            self.ast.identifier(self.id.expect("IdentId exists"))
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::ids::StmtId;
    use crate::ast::{AstNodePrettyPrint, WithoutImplicitRet};
    use crate::desugar::ImplicitRet;
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

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

        let ast = ast1
            .merge(ast2)
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        let xml = XmlWriter::new(&ast).serialize();

        assert_snapshot!(&xml);
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

        let ast = ast1
            .merge(ast2)
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        let xml = XmlWriter::new(&ast).serialize();

        assert_snapshot!(&xml);
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

        let ast = ast1
            .merge(ast2)
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        let xml = XmlWriter::new(&ast).serialize();

        assert_snapshot!(&xml);
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

        let ast = ast1
            .merge(ast2)
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        let xml = XmlWriter::new(&ast).serialize();

        assert_snapshot!(&xml);
    }
}
