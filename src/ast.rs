pub mod expression;
pub mod identifier;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{ExprId, Expression, ExpressionKind};
use crate::ast::identifier::IdentId;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Statement, StatementKind, StmtId};
use std::fmt::{Display, Formatter};

pub trait Visitor<R> {
    fn visit_ast(&mut self, ast: &Ast) -> R;

    fn visit_statement(&mut self, stmt: StmtId) -> R;

    fn visit_expression(&mut self, expr: ExprId) -> R;

    fn visit_literal(&mut self, literal: &Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    identifiers: Vec<String>,
    expressions: Vec<Expression>,
    statements: Vec<Statement>,
    // todo replace with Statements
    root: Vec<StmtId>,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        expressions: Vec<Expression>,
        statements: Vec<Statement>,
        root: Vec<StmtId>,
    ) -> Self {
        assert!(!root.is_empty());
        Self {
            identifiers,
            expressions,
            statements,
            root,
        }
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifier(&self, id: IdentId) -> &String {
        &self.identifiers[id.id()]
    }

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id.id()]
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id.id()]
    }
}

pub struct PrettyPrint<'a, T> {
    indent: usize,
    ast: &'a Ast,
    id: T,
}

impl<'a, T> PrettyPrint<'a, T> {
    pub fn new(ast: &'a Ast, id: T) -> Self {
        Self { indent: 0, ast, id }
    }

    fn new_with_ident(ast: &'a Ast, id: T, ident: usize) -> Self {
        Self {
            indent: ident,
            ast,
            id,
        }
    }
}

impl Display for PrettyPrint<'_, StmtId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.statement(self.id).kind() {
            StatementKind::Expression(expr) => {
                let semi = match self.ast.expression(*expr).kind() {
                    ExpressionKind::If(_, _, _) | ExpressionKind::While(_, _)=> "",
                    _ => ";",
                };
                writeln!(
                    f,
                    "{indent}{}{semi}",
                    PrettyPrint::new_with_ident(self.ast, *expr, self.indent)
                )
            }
            StatementKind::Let(ident, expr) => {
                writeln!(
                    f,
                    "{indent}let {} = {};",
                    PrettyPrint::new(self.ast, ident.id()),
                    PrettyPrint::new(self.ast, *expr),
                )
            }
            StatementKind::Ret(expr) => {
                writeln!(f, "{indent}ret {};", PrettyPrint::new(self.ast, *expr))
            }
            StatementKind::LetFn(ident, params, stmts) => {
                write!(f, "{indent}let {}(", PrettyPrint::new(self.ast, ident.id()))?;
                for (i, param) in params.iter().enumerate() {
                    write!(f, "{}", PrettyPrint::new(self.ast, param.id()))?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                writeln!(f, ") = {{")?;
                for stmt in stmts {
                    write!(
                        f,
                        "{indent}{}",
                        PrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                    )?;
                }
                writeln!(f, "{indent}}}")
            }
        }
    }
}

impl Display for PrettyPrint<'_, ExprId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.expression(self.id).kind() {
            ExpressionKind::Assignment(ident, expr) => {
                write!(
                    f,
                    "{} = {}",
                    PrettyPrint::new(self.ast, ident.id()),
                    PrettyPrint::new(self.ast, *expr)
                )
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                writeln!(f, "if {} {{", PrettyPrint::new(self.ast, *cond))?;
                for stmt in true_branch {
                    write!(
                        f,
                        "{}",
                        PrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                    )?;
                }
                if !false_branch.is_empty() {
                    writeln!(f, "}}")?;
                    writeln!(f, "else {{")?;
                    for stmt in false_branch {
                        write!(
                            f,
                            "{}",
                            PrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                        )?;
                    }
                }
                write!(f, "{indent}}}")
            }
            ExpressionKind::Literal(lit) => match lit.kind() {
                LiteralKind::Boolean(b) => write!(f, "{b}"),
                LiteralKind::Identifier(ident) => {
                    write!(f, "{}", PrettyPrint::new(self.ast, ident.id()))
                }
                LiteralKind::Number(n) => write!(f, "{n}"),
            },
            ExpressionKind::Binary(left, op, right) => {
                write!(
                    f,
                    "{} {} {}",
                    PrettyPrint::new(self.ast, *left),
                    op.kind(),
                    PrettyPrint::new(self.ast, *right)
                )
            }
            ExpressionKind::FunctionCall(ident, params) => {
                write!(f, "{}(", PrettyPrint::new(self.ast, ident.id()))?;
                for (i, expr) in params.iter().enumerate() {
                    write!(f, "{}", PrettyPrint::new(self.ast, *expr))?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            ExpressionKind::Unary(op, expr) => {
                write!(f, "{} {}", op.kind(), PrettyPrint::new(self.ast, *expr))
            }
            ExpressionKind::While(cond, stmts) => {
                writeln!(f, "while {} {{", PrettyPrint::new(self.ast, *cond))?;
                for stmt in stmts {
                    write!(
                        f,
                        "{}",
                        PrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                    )?;
                }
                writeln!(f, "}}")
            }
        }
    }
}

impl Display for PrettyPrint<'_, IdentId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        write!(f, "{indent}{}", self.ast.identifier(self.id))
    }
}
