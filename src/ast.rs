pub mod expression;
pub mod identifier;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::IdentifierRef;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Statement, StatementKind};
use std::fmt::{Display, Formatter};

pub trait Visitor<R> {
    fn visit_statement(&mut self, stmt: StmtId) -> R;

    fn visit_expression(&mut self, expr: ExprId) -> R;

    fn visit_literal(&mut self, literal: &Literal) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    /// Unique identifiers names
    identifiers: Vec<String>,
    /// Identifier refs
    identifier_refs: Vec<IdentifierRef>,
    /// All expressions
    expressions: Vec<Expression>,
    /// All statements
    statements: Vec<Statement>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef>,
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
        }
    }

    pub fn statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id.id()]
    }

    #[cfg(test)]
    pub fn identifier_id(&self, name: &str) -> IdentId {
        for (id, ident) in self.identifiers.iter().enumerate() {
            if ident == name {
                return IdentId::from(id);
            }
        }
        panic!("Identifier {} not found", name)
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef {
        &self.identifier_refs[id.id()]
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

    pub fn replace_identifier_ref(&mut self, ident_ref: IdentifierRef) {
        let id = ident_ref.id().id();
        self.identifier_refs[id] = ident_ref;
    }

    pub fn replace_expression(&mut self, expression: Expression) {
        let id = expression.id().id();
        self.expressions[id] = expression
    }

    pub fn replace_statement(&mut self, statement: Statement) {
        let id = statement.id().id();
        self.statements[id] = statement
    }
}

pub struct AstNodePrettyPrint<'a, T> {
    indent: usize,
    ast: &'a Ast,
    id: T,
}

impl<'a, T> AstNodePrettyPrint<'a, T> {
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

impl Display for AstNodePrettyPrint<'_, StmtId> {
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
                    AstNodePrettyPrint::new_with_ident(self.ast, *expr, self.indent)
                )
            }
            StatementKind::Let(ident, expr) => {
                writeln!(
                    f,
                    "{indent}let {} = {};",
                    AstNodePrettyPrint::new(self.ast, ident.id()),
                    AstNodePrettyPrint::new(self.ast, *expr),
                )
            }
            StatementKind::Ret(expr) => {
                writeln!(
                    f,
                    "{indent}ret {};",
                    AstNodePrettyPrint::new(self.ast, *expr)
                )
            }
            StatementKind::LetFn(ident, params, ty, expr) => {
                write!(
                    f,
                    "{indent}let {}(",
                    AstNodePrettyPrint::new(self.ast, ident.id())
                )?;
                for (i, param) in params.iter().enumerate() {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new(self.ast, param.identifier().id())
                    )?;
                    write!(f, ": ")?;
                    write!(f, "{}", AstNodePrettyPrint::new(self.ast, param.ty().id()))?;
                    if i < params.len() - 1 {
                        write!(f, ", ")?;
                    }
                }

                let ty = ty
                    .as_ref()
                    .map(|ty| format!(": {}", AstNodePrettyPrint::new(self.ast, ty.id())))
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
                        AstNodePrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                    )?;
                }
                writeln!(f, "{indent}}}")
            }
        }
    }
}

impl Display for AstNodePrettyPrint<'_, ExprId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        match self.ast.expression(self.id).kind() {
            ExpressionKind::Assignment(ident, expr) => {
                let ident = self.ast.identifier_ref(*ident).ident();
                write!(
                    f,
                    "{} = {}",
                    AstNodePrettyPrint::new(self.ast, ident.id()),
                    AstNodePrettyPrint::new(self.ast, *expr)
                )
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                writeln!(f, "if {} {{", AstNodePrettyPrint::new(self.ast, *cond))?;

                let true_branch = match self.ast.expression(*true_branch).kind() {
                    ExpressionKind::Block(true_branch) => true_branch,
                    _ => panic!("block expected"),
                };

                for stmt in true_branch {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                    )?;
                }
                if let Some(false_branch) = false_branch {
                    writeln!(f, "}}")?;
                    writeln!(f, "else {{")?;

                    let false_branch = match self.ast.expression(*false_branch).kind() {
                        ExpressionKind::Block(true_branch) => true_branch,
                        _ => panic!("block expected"),
                    };

                    for stmt in false_branch {
                        write!(
                            f,
                            "{}",
                            AstNodePrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
                        )?;
                    }
                }
                write!(f, "{indent}}}")
            }
            ExpressionKind::Literal(lit) => match lit.kind() {
                LiteralKind::Boolean(b) => write!(f, "{b}"),
                LiteralKind::Identifier(ident) => {
                    let ident = self.ast.identifier_ref(*ident).ident();
                    write!(f, "{}", AstNodePrettyPrint::new(self.ast, ident.id()))
                }
                LiteralKind::Number(n) => write!(f, "{n}"),
            },
            ExpressionKind::Binary(left, op, right) => {
                write!(
                    f,
                    "{} {} {}",
                    AstNodePrettyPrint::new(self.ast, *left),
                    op.kind(),
                    AstNodePrettyPrint::new(self.ast, *right)
                )
            }
            ExpressionKind::FunctionCall(ident, params) => {
                let ident = self.ast.identifier_ref(*ident).ident();
                write!(f, "{}(", AstNodePrettyPrint::new(self.ast, ident.id()))?;
                for (i, expr) in params.iter().enumerate() {
                    write!(f, "{}", AstNodePrettyPrint::new(self.ast, *expr))?;
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
                    AstNodePrettyPrint::new(self.ast, *expr)
                )
            }
            ExpressionKind::While(cond, expr) => {
                writeln!(f, "while {} {{", AstNodePrettyPrint::new(self.ast, *cond))?;

                let stmts = match self.ast.expression(*expr).kind() {
                    ExpressionKind::Block(stmts) => stmts,
                    _ => panic!("block expected"),
                };

                for stmt in stmts {
                    write!(
                        f,
                        "{}",
                        AstNodePrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
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
                        AstNodePrettyPrint::new_with_ident(self.ast, *stmt, self.indent + 1)
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

#[cfg(test)]
mod tests {
    use crate::ast::AstNodePrettyPrint;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    #[test]
    fn pretty_print() {
        let ast = Parser::new(Lexer::new(
            r#"
        let fact(n: number): number = {
            if n < 0 {
                ret 0;
            }
            let product = 1;
            while n > 0 {
                product = product * n;
                n = n - 1;
            }
            product;
        }
    "#,
        ))
        .parse()
        .0;

        let actual = format!(
            "{}",
            AstNodePrettyPrint::new(&ast, *ast.statements().first().unwrap())
        );
        let expected = r#"let fact(n: number): number = {
  if n < 0 {
    ret 0;
  }
  let product = 1;
  while n > 0 {
    product = product * n;
    n = n - 1;
  }

  product;
}
"#;
        assert_eq!(actual, expected);
    }
}

impl Display for AstNodePrettyPrint<'_, IdentId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        write!(f, "{indent}{}", self.ast.identifier(self.id))
    }
}
