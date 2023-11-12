use crate::ast::expression::ExpressionKind;
use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, IdentId, ScopeId, StmtId, SymbolId};
use crate::ast::literal::Literal;
use crate::ast::statement::StatementKind;
use crate::ast::{Ast, Visitor};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

pub struct SymbolTableGen<'a> {
    ast: &'a mut Ast,
    symbols: Vec<Symbol>,
    scopes: Vec<Scope>,
    scopes_stack: Vec<ScopeId>,
}

impl<'a> SymbolTableGen<'a> {
    pub fn new(ast: &'a mut Ast) -> Self {
        let scope = ScopeId::from(0);
        Self {
            ast,
            symbols: vec![],
            scopes: vec![Scope::root(scope)],
            scopes_stack: vec![scope],
        }
    }

    pub fn build_table(mut self) -> SymbolTable {
        let statements = self.ast.statements().to_vec();

        for stmt in statements {
            self.visit_statement(stmt);
        }

        SymbolTable::new(self.symbols, self.scopes)
    }

    fn push_scope(&mut self) {
        let child_id = ScopeId::from(self.scopes.len());
        let parent = self
            .scopes
            .get_mut(
                self.scopes_stack
                    .last()
                    .expect("there is a current scope")
                    .id(),
            )
            .expect("scope exists");
        let child = parent.child(child_id);
        self.scopes.push(child);
        self.scopes_stack.push(child_id);
    }

    fn push_sub_scope(&mut self) {
        self.push_scope();
        // the last pushed scope replaces the previous one (we dont want a nested scope, but a
        // sub-scope)
        self.scopes_stack.swap_remove(self.scopes_stack.len() - 2);
    }

    fn pop_scope(&mut self) {
        self.scopes_stack.pop();
    }

    fn insert(&mut self, ident: IdentId, node: Node) {
        let scope_id = self.scopes_stack.last().expect("there is a current scope");
        let scope = self.scopes.get_mut(scope_id.id()).expect("scope exists");
        let symbol_id = SymbolId::from(self.symbols.len());
        let symbol = Symbol {
            id: symbol_id,
            scope_id: *scope_id,
            node,
        };
        self.symbols.push(symbol);
        scope.insert(ident, symbol_id);
    }
}

impl<'a> Visitor<()> for SymbolTableGen<'a> {
    fn visit_statement(&mut self, stmt: StmtId) {
        let scope_id = *self.scopes_stack.last().expect("current scope exists");

        let statement = {
            let mut statement = self.ast.statement(stmt).clone();
            statement.set_scope(scope_id);
            self.ast.replace_statement(statement.clone());
            statement
        };

        match statement.kind() {
            StatementKind::Let(ident, expr) => {
                self.visit_expression(*expr);
                self.push_sub_scope();
                self.insert(ident.id(), Node::LetStatement(stmt));
            }
            StatementKind::LetFn(ident, params, expr) => {
                self.insert(ident.id(), Node::LetFnStatement(stmt));

                {
                    self.push_scope();
                    for param in params {
                        self.insert(param.id(), Node::Parameter(param.clone()));
                    }

                    self.visit_expression(*expr);

                    self.pop_scope();
                }
            }
            StatementKind::Expression(expr) => {
                self.visit_expression(*expr);
            }
            StatementKind::Ret(expr) => {
                self.visit_expression(*expr);
            }
        };
    }

    fn visit_expression(&mut self, expr: ExprId) {
        let scope_id = *self.scopes_stack.last().expect("current scope exists");

        let expression = {
            let mut expression = self.ast.expression(expr).clone();
            expression.set_scope(scope_id);
            self.ast.replace_expression(expression.clone());
            expression
        };

        match expression.kind() {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(*expr);
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_expression(*cond);
                self.visit_expression(*true_branch);

                if let Some(false_branch) = false_branch {
                    self.visit_expression(*false_branch);
                }
            }
            ExpressionKind::Literal(_lit) => {
                // nothing to do
            }
            ExpressionKind::Binary(left, _, right) => {
                let left = *left;
                let right = *right;
                self.visit_expression(left);
                self.visit_expression(right);
            }
            ExpressionKind::FunctionCall(_, params) => {
                let params = params.to_vec();
                for param in params {
                    self.visit_expression(param);
                }
            }
            ExpressionKind::Unary(_, expr) => {
                self.visit_expression(*expr);
            }
            ExpressionKind::While(cond, expr) => {
                self.visit_expression(*cond);
                self.visit_expression(*expr);
            }
            ExpressionKind::Block(stmts) => {
                self.push_scope();
                for stmt in stmts {
                    self.visit_statement(*stmt);
                }
                self.pop_scope();
            }
            ExpressionKind::Dummy => {
                // nothing to do
            }
        }
    }

    fn visit_literal(&mut self, _literal: &Literal) {
        unimplemented!()
    }
}

#[derive(PartialEq)]
pub struct Scope {
    id: ScopeId,
    parent: Option<ScopeId>,
    children: Vec<ScopeId>,
    symbols: HashMap<IdentId, SymbolId>,
}

impl Scope {
    pub fn root(id: ScopeId) -> Scope {
        Self {
            id,
            parent: None,
            children: Vec::new(),
            symbols: Default::default(),
        }
    }

    fn child(&mut self, id: ScopeId) -> Scope {
        self.children.push(id);
        Self {
            id,
            parent: Some(self.id),
            children: Vec::new(),
            symbols: Default::default(),
        }
    }

    fn insert(&mut self, identifier: IdentId, symbol_id: SymbolId) {
        self.symbols.insert(identifier, symbol_id);
    }

    pub fn get(&self, identifier: IdentId) -> Option<SymbolId> {
        self.symbols.get(&identifier).cloned()
    }
}

impl Debug for Scope {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SymbolTable {{ symbols: {:?} children: {:?} }}",
            self.symbols, self.children
        )
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    id: SymbolId,
    /// points to the scope where this symbol is defined
    scope_id: ScopeId,
    /// the AST node that defines that symbol
    node: Node,
}

impl Symbol {
    pub fn id(&self) -> SymbolId {
        self.id
    }

    pub fn node(&self) -> &Node {
        &self.node
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Node {
    LetStatement(StmtId),
    LetFnStatement(StmtId),
    Parameter(Identifier),
}

#[derive(Debug, PartialEq)]
pub struct SymbolTable {
    symbols: Vec<Symbol>,
    scopes: Vec<Scope>,
}

impl SymbolTable {
    fn new(symbols: Vec<Symbol>, scopes: Vec<Scope>) -> Self {
        Self { symbols, scopes }
    }

    pub fn find(&self, identifier: IdentId, scope: ScopeId) -> Option<Symbol> {
        let scope = &self.scopes[scope.id()];
        if let Some(symbol) = scope.get(identifier) {
            Some(self.symbols[symbol.id()].clone())
        } else if let Some(parent) = scope.parent {
            self.find(identifier, parent)
        } else {
            None
        }
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.id()]
    }
}

pub struct ScopePrettyPrint<'a> {
    indent: usize,
    table: &'a SymbolTable,
    ast: &'a Ast,
    id: ScopeId,
}

impl<'a> ScopePrettyPrint<'a> {
    pub fn new(table: &'a SymbolTable, ast: &'a Ast, id: ScopeId) -> Self {
        let mut indent = 0;
        let mut parent_id = id;
        while let Some(id) = table.scopes[parent_id.id()].parent {
            parent_id = id;
            indent += 1;
        }

        Self {
            indent,
            table,
            ast,
            id,
        }
    }

    fn new_with_indent(table: &'a SymbolTable, ast: &'a Ast, id: ScopeId, indent: usize) -> Self {
        Self {
            indent,
            table,
            ast,
            id,
        }
    }
}

impl Display for ScopePrettyPrint<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let indent = "|  ".repeat(self.indent);
        writeln!(f, "{indent}Table {}:", self.id.id())?;
        for (ident, symbol) in self.table.scopes[self.id.id()].symbols.iter() {
            let symbol = &self.table.symbols[symbol.id()];
            let symbol_span = match &symbol.node {
                Node::LetStatement(s) => self.ast.statement(*s).span(),
                Node::LetFnStatement(s) => self.ast.statement(*s).span(),
                Node::Parameter(i) => i.span(),
            };
            writeln!(
                f,
                "{indent}  {} -> {}:{}",
                self.ast.identifier(*ident),
                symbol_span.line(),
                symbol_span.column(),
            )?;
        }
        if let Some(parent_id) = self.table.scopes[self.id.id()].parent {
            writeln!(
                f,
                "{}",
                ScopePrettyPrint::new_with_indent(self.table, self.ast, parent_id, self.indent - 1)
            )?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::ids::{IdentId, ScopeId, StmtId, SymbolId};
    use crate::lexer::{Lexer, Span};
    use crate::parser::Parser;

    #[test]
    fn top_level_function_with_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { }")).parse().0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = SymbolTable {
            symbols: vec![
                Symbol {
                    id: SymbolId::from(0),
                    scope_id: ScopeId::from(0),
                    node: Node::LetFnStatement(StmtId::from(0)),
                },
                Symbol {
                    id: SymbolId::from(1),
                    scope_id: ScopeId::from(1),
                    node: Node::Parameter(Identifier::new(
                        ast.identifier_id("n"),
                        Span::new(1, 7, 6, 1),
                    )),
                },
            ],
            scopes: vec![
                Scope {
                    id: ScopeId::from(0),
                    parent: None,
                    children: vec![ScopeId::from(1)],
                    symbols: vec![(ast.identifier_id("f"), SymbolId::from(0))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(1),
                    parent: Some(ScopeId::from(0)),
                    children: vec![ScopeId::from(2)],
                    symbols: vec![(ast.identifier_id("n"), SymbolId::from(1))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(2),
                    parent: Some(ScopeId::from(1)),
                    children: vec![],
                    symbols: Default::default(),
                },
            ],
        };

        assert_eq!(table, expected);
    }

    #[test]
    fn top_level_function_with_used_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { n; }")).parse().0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = SymbolTable {
            symbols: vec![
                Symbol {
                    id: SymbolId::from(0),
                    scope_id: ScopeId::from(0),
                    node: Node::LetFnStatement(StmtId::from(1)),
                },
                Symbol {
                    id: SymbolId::from(1),
                    scope_id: ScopeId::from(1),
                    node: Node::Parameter(Identifier::new(
                        ast.identifier_id("n"),
                        Span::new(1, 7, 6, 1),
                    )),
                },
            ],
            scopes: vec![
                Scope {
                    id: ScopeId::from(0),
                    parent: None,
                    children: vec![ScopeId::from(1)],
                    symbols: vec![(ast.identifier_id("f"), SymbolId::from(0))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(1),
                    parent: Some(ScopeId::from(0)),
                    children: vec![ScopeId::from(2)],
                    symbols: vec![(ast.identifier_id("n"), SymbolId::from(1))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(2),
                    parent: Some(ScopeId::from(1)),
                    children: vec![],
                    symbols: HashMap::default(),
                },
            ],
        };

        assert_eq!(table, expected);
    }

    #[test]
    fn top_level_function_with_variable() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { let m = 0; }"))
            .parse()
            .0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = SymbolTable {
            symbols: vec![
                Symbol {
                    id: SymbolId::from(0),
                    scope_id: ScopeId::from(0),
                    node: Node::LetFnStatement(StmtId::from(1)),
                },
                Symbol {
                    id: SymbolId::from(1),
                    scope_id: ScopeId::from(1),
                    node: Node::Parameter(Identifier::new(
                        ast.identifier_id("n"),
                        Span::new(1, 7, 6, 1),
                    )),
                },
                Symbol {
                    id: SymbolId::from(2),
                    scope_id: ScopeId::from(3),
                    node: Node::LetStatement(StmtId::from(0)),
                },
            ],
            scopes: vec![
                Scope {
                    id: ScopeId::from(0),
                    parent: None,
                    children: vec![ScopeId::from(1)],
                    symbols: vec![(ast.identifier_id("f"), SymbolId::from(0))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(1),
                    parent: Some(ScopeId::from(0)),
                    children: vec![ScopeId::from(2)],
                    symbols: vec![(ast.identifier_id("n"), SymbolId::from(1))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(2),
                    parent: Some(ScopeId::from(1)),
                    children: vec![ScopeId::from(3)],
                    symbols: HashMap::default(),
                },
                Scope {
                    id: ScopeId::from(3),
                    parent: Some(ScopeId::from(2)),
                    children: vec![],
                    symbols: vec![(ast.identifier_id("m"), SymbolId::from(2))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
            ],
        };

        assert_eq!(table, expected);
    }

    #[test]
    fn top_level_function_with_redefined_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { let n = 0; }"))
            .parse()
            .0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = SymbolTable {
            symbols: vec![
                Symbol {
                    id: SymbolId::from(0),
                    scope_id: ScopeId::from(0),
                    node: Node::LetFnStatement(StmtId::from(1)),
                },
                Symbol {
                    id: SymbolId::from(1),
                    scope_id: ScopeId::from(1),
                    node: Node::Parameter(Identifier::new(
                        ast.identifier_id("n"),
                        Span::new(1, 7, 6, 1),
                    )),
                },
                Symbol {
                    id: SymbolId::from(2),
                    scope_id: ScopeId::from(3),
                    node: Node::LetStatement(StmtId::from(0)),
                },
            ],
            scopes: vec![
                Scope {
                    id: ScopeId::from(0),
                    parent: None,
                    children: vec![ScopeId::from(1)],
                    symbols: vec![(ast.identifier_id("f"), SymbolId::from(0))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(1),
                    parent: Some(ScopeId::from(0)),
                    children: vec![ScopeId::from(2)],
                    symbols: vec![(ast.identifier_id("n"), SymbolId::from(1))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
                Scope {
                    id: ScopeId::from(2),
                    parent: Some(ScopeId::from(1)),
                    children: vec![ScopeId::from(3)],
                    symbols: HashMap::default(),
                },
                Scope {
                    id: ScopeId::from(3),
                    parent: Some(ScopeId::from(2)),
                    children: vec![],
                    symbols: vec![(ast.identifier_id("n"), SymbolId::from(2))]
                        .into_iter()
                        .collect::<HashMap<IdentId, SymbolId>>(),
                },
            ],
        };

        assert_eq!(table, expected);
    }

    #[test]
    fn find_in_scope() {
        let mut ast = Parser::new(Lexer::new(
            "let f(n) = { let m = 0; let p = 0; let p = n + m; let q = p; }",
        ))
        .parse()
        .0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        let let_second_p_stmt = ast.statement(ast.statement_id(35));

        match table
            .find(
                ast.identifier_id("p"),
                let_second_p_stmt.scope().expect("scope exists"),
            )
            .expect("p is in scope")
            .node
        {
            Node::LetStatement(stmt) => {
                assert_eq!(ast.statement(stmt).span().start(), 24);
            }
            _ => panic!("statement expected"),
        }

        match table
            .find(
                ast.identifier_id("n"),
                let_second_p_stmt.scope().expect("scope exists"),
            )
            .expect("n is in scope")
            .node
        {
            Node::Parameter(ident) => {
                assert_eq!(ident.span().start(), 6);
            }
            _ => panic!("statement expected"),
        }

        match table
            .find(
                ast.identifier_id("m"),
                let_second_p_stmt.scope().expect("scope exists"),
            )
            .expect("m is in scope")
            .node
        {
            Node::LetStatement(stmt) => {
                assert_eq!(ast.statement(stmt).span().start(), 13);
            }
            _ => panic!("statement expected"),
        }

        let let_q_stmt = ast.statement(ast.statement_id(50));

        match table
            .find(
                ast.identifier_id("p"),
                let_q_stmt.scope().expect("scope exists"),
            )
            .expect("p is in scope")
            .node
        {
            Node::LetStatement(stmt) => {
                assert_eq!(ast.statement(stmt).span().start(), 35);
            }
            _ => panic!("statement expected"),
        }
    }

    #[test]
    fn if_statement() {
        let mut ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                let a = 0;
                if true {
                    let b = 42;
                    b;
                }
                else if false {
                    let c = 42;
                    c;
                }
                else {
                    let d = 42;
                    d;
                }
                let e = 42;
                e;
            }"#,
        ))
        .parse()
        .0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        {
            let stmt = ast.statement_id(41);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            assert!(table.find(ast.identifier_id("a"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("b"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("c"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("d"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("e"), scope_id).is_none());
        }

        {
            let stmt = ast.statement_id(130);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            let symbol = table
                .find(ast.identifier_id("a"), scope_id)
                .expect("a is in scope");
            match symbol.node {
                Node::LetStatement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 41);
                }
                _ => panic!("statement expected"),
            }
            let symbol = table
                .find(ast.identifier_id("b"), scope_id)
                .expect("a is in scope");
            match symbol.node {
                Node::LetStatement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 98);
                }
                _ => panic!("statement expected"),
            }
            assert!(table.find(ast.identifier_id("c"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("d"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("e"), scope_id).is_none());
        }

        {
            let stmt = ast.statement_id(235);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            let symbol = table
                .find(ast.identifier_id("c"), scope_id)
                .expect("c is in scope");
            match symbol.node {
                Node::LetStatement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 203);
                }
                _ => panic!("statement expected"),
            }
            assert!(table.find(ast.identifier_id("b"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("d"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("e"), scope_id).is_none());
        }

        {
            let c_stmt = ast.statement_id(331);
            let scope_id = ast.statement(c_stmt).scope().expect("scope exists");
            let symbol = table
                .find(ast.identifier_id("d"), scope_id)
                .expect("d is in scope");
            match symbol.node {
                Node::LetStatement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 299);
                }
                _ => panic!("statement expected"),
            }
            assert!(table.find(ast.identifier_id("b"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("c"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("e"), scope_id).is_none());
        }

        {
            let stmt = ast.statement_id(396);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            assert!(table.find(ast.identifier_id("a"), scope_id).is_some());
            assert!(table.find(ast.identifier_id("b"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("c"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("d"), scope_id).is_none());
            assert!(table.find(ast.identifier_id("e"), scope_id).is_some());
        }
    }

    #[test]
    fn while_statement() {
        let mut ast = Parser::new(Lexer::new(
            "let x() = { while true { let a = 42; a; } let b = 42; }",
        ))
        .parse()
        .0;

        let table = SymbolTableGen::new(&mut ast).build_table();

        {
            let stmt = ast.statement_id(37);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            let symbol = table
                .find(ast.identifier_id("a"), scope_id)
                .expect("a is in scope");
            match symbol.node {
                Node::LetStatement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 25);
                }
                _ => panic!("statement expected"),
            }
        }

        {
            let stmt = ast.statement_id(42);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            assert!(table.find(ast.identifier_id("a"), scope_id).is_none());
        }
    }
}
