pub mod expression;
pub mod identifier;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::{Identifier, IdentifierRef};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Parameter, Statement, StatementKind};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

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

    pub fn merge(self, other: Ast) -> Ast {
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
                    StatementKind::Ret(expr) => {
                        StatementKind::Ret(ExprId::from(expr_base + expr.id()))
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

        Ast::new(identifiers, identifier_refs, expressions, statements, root)
    }

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

    pub fn create_identifier_ref(
        &mut self,
        identifier: Identifier,
        symbol: SymbolId,
    ) -> IdentRefId {
        let id = IdentRefId::from(self.identifier_refs.len());
        let mut identifier_ref = IdentifierRef::new(id, identifier);
        identifier_ref.set_symbol_id(symbol);
        self.identifier_refs.push(identifier_ref);
        id
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

impl Default for Ast {
    fn default() -> Self {
        Self::new(vec![], vec![], vec![], vec![], vec![])
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

    #[test]
    fn merge_1() {
        let (ast1, d) = Parser::new(Lexer::new(
            "let x_1 = 0; let f_1(p_1: number): boolean = { p_1 == 1; } f_1(x_1);",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let (ast2, d) = Parser::new(Lexer::new(
            "let x_2 = 0; let f_2(p_2: number): boolean = { p_2 == 2; } f_2(x_2);",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let ast = ast1.merge(ast2);

        let (ast, symbols, expr_types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        let xml = XmlWriter::new(&ast, &symbols, &expr_types).serialize();

        assert_snapshot!(&xml);
    }

    #[test]
    fn merge_2() {
        let (ast1, d) = Parser::new(Lexer::new("let x_1 = 0; x_1 = -x_1 * 2;")).parse();
        assert!(d.is_empty(), "{:?}", d);

        let (ast2, d) = Parser::new(Lexer::new("let x_2 = 0; x_2 = -x_2 * 2;")).parse();
        assert!(d.is_empty(), "{:?}", d);

        let ast = ast1.merge(ast2);

        let (ast, symbols, expr_types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        let xml = XmlWriter::new(&ast, &symbols, &expr_types).serialize();

        assert_snapshot!(&xml);
    }

    #[test]
    fn merge_if() {
        let (ast1, d) = Parser::new(Lexer::new(
            "let c_1 = true; let t_1 = 1; let f_1 = 0; if c_1 { t_1; } else { f_1; }",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let (ast2, d) = Parser::new(Lexer::new(
            "let c_2 = true; let t_2 = 1; let f_2 = 0; if c_2 { t_2; } else { f_2; }",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let ast = ast1.merge(ast2);

        let (ast, symbols, expr_types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        let xml = XmlWriter::new(&ast, &symbols, &expr_types).serialize();

        assert_snapshot!(&xml);
    }

    #[test]
    fn merge_while() {
        let (ast1, d) = Parser::new(Lexer::new(
            "let c_1 = true; let w_1 = 1; while c_1 { w_1; }",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let (ast2, d) = Parser::new(Lexer::new(
            "let c_2 = false; let w_2 = 2; while c_2 { w_2; }",
        ))
        .parse();
        assert!(d.is_empty(), "{:?}", d);

        let ast = ast1.merge(ast2);

        let (ast, symbols, expr_types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        let xml = XmlWriter::new(&ast, &symbols, &expr_types).serialize();

        assert_snapshot!(&xml);
    }
}

impl Display for AstNodePrettyPrint<'_, IdentId> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "  ".repeat(self.indent);
        write!(f, "{indent}{}", self.ast.identifier(self.id))
    }
}
