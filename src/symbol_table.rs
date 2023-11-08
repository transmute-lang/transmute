use crate::ast::expression::{ExprId, ExpressionKind};
use crate::ast::identifier::{IdentId, Identifier};
use crate::ast::literal::Literal;
use crate::ast::statement::{StatementKind, StmtId};
use crate::ast::{Ast, Visitor};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};

pub struct SymbolTableGen<'a> {
    ast: &'a mut Ast,
    scopes: Vec<Scope>,
    scopes_stack: Vec<ScopeId>,
}

impl<'a> SymbolTableGen<'a> {
    pub fn new(ast: &'a mut Ast) -> Self {
        let scope = ScopeId::from(0);
        Self {
            ast,
            scopes: vec![Scope::root(scope)],
            scopes_stack: vec![scope],
        }
    }

    pub fn build_table(mut self) -> SymbolTable {
        let statements = self.ast.statements().to_vec();

        for stmt in statements {
            self.visit_statement(stmt);
        }

        SymbolTable::new(self.scopes)
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
        scope.insert(*scope_id, ident, node);
    }
}

impl<'a> Visitor<()> for SymbolTableGen<'a> {
    fn visit_ast(&mut self, _ast: &Ast) {
        unimplemented!("useless")
    }

    fn visit_statement(&mut self, stmt: StmtId) {
        let scope_id = *self.scopes_stack.last().expect("scope exists");

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
                self.insert(ident.id(), Node::Statement(stmt));
            }
            StatementKind::LetFn(ident, params, expr) => {
                self.insert(ident.id(), Node::Statement(stmt));

                {
                    self.push_scope();
                    for param in params {
                        self.insert(param.id(), Node::Identifier(param.clone()));
                    }

                    let statements = match self.ast.expression(*expr).kind() {
                        ExpressionKind::Block(stmts) => stmts.to_vec(),
                        _ => panic!("block expected"),
                    };
                    for statement in statements {
                        self.visit_statement(statement);
                    }

                    self.pop_scope();
                }
            }
            StatementKind::Expression(expr) => {
                self.visit_expression(*expr);
            }
            _ => {}
        };
    }

    fn visit_expression(&mut self, expr: ExprId) {
        match self.ast.expression(expr).kind() {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(*expr);
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let true_branch = match self.ast.expression(*true_branch).kind() {
                    ExpressionKind::Block(stmts) => stmts.to_vec(),
                    _ => panic!("block expected"),
                };
                let false_branch = if let Some(false_branch) = false_branch {
                    match self.ast.expression(*false_branch).kind() {
                        ExpressionKind::Block(stmts) => stmts.to_vec(),
                        _ => panic!("block expected"),
                    }
                } else {
                    vec![]
                };

                self.visit_expression(*cond);
                if !true_branch.is_empty() {
                    self.push_scope();
                    for stmt in true_branch {
                        self.visit_statement(stmt);
                    }
                    self.pop_scope();
                }

                if !false_branch.is_empty() {
                    self.push_scope();
                    for stmt in false_branch {
                        self.visit_statement(stmt);
                    }
                    self.pop_scope();
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
                let stmts = match self.ast.expression(*expr).kind() {
                    ExpressionKind::Block(stmts) => stmts.to_vec(),
                    _ => panic!("block expected"),
                };
                self.visit_expression(*cond);
                if !stmts.is_empty() {
                    self.push_scope();
                    for stmt in stmts {
                        self.visit_statement(stmt);
                    }
                    self.pop_scope();
                }
            }
            ExpressionKind::Block(_) => {
                todo!("implement block expressions")
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
    symbols: HashMap<IdentId, Symbol>,
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

    fn insert(&mut self, scope_id: ScopeId, identifier: IdentId, node: Node) {
        self.symbols.insert(identifier, Symbol { scope_id, node });
    }

    pub fn get(&self, identifier: IdentId) -> Option<Symbol> {
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct ScopeId {
    id: usize,
}

impl ScopeId {
    fn id(&self) -> usize {
        self.id
    }
}

impl From<usize> for ScopeId {
    fn from(id: usize) -> Self {
        Self { id }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    /// points to the symbol table of that symbol
    scope_id: ScopeId,
    /// the AST node that defines that symbol
    node: Node,
}

#[derive(Debug, Clone, PartialEq)]
enum Node {
    // only a Let or a LetFn
    Statement(StmtId),
    Identifier(Identifier),
}

#[derive(Debug)]
pub struct SymbolTable {
    scopes: Vec<Scope>,
}

impl SymbolTable {
    fn new(scopes: Vec<Scope>) -> Self {
        Self { scopes }
    }

    pub fn find(&self, identifier: IdentId, scope: ScopeId) -> Option<Symbol> {
        let scope = &self.scopes[scope.id()];
        if let Some(symbol) = scope.get(identifier) {
            Some(symbol)
        } else if let Some(parent) = scope.parent {
            self.find(identifier, parent)
        } else {
            None
        }
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
            let symbol_span = match &symbol.node {
                Node::Statement(s) => self.ast.statement(*s).span(),
                Node::Identifier(i) => i.span(),
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
    use crate::lexer::{Lexer, Span};
    use crate::parser::Parser;

    #[test]
    fn top_level_function_with_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { }"))
            .parse()
            .expect("source is valid");

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = vec![
            Scope {
                id: ScopeId::from(0),
                parent: None,
                children: vec![ScopeId::from(1)],
                symbols: vec![(
                    ast.identifier_id("f"),
                    Symbol {
                        scope_id: ScopeId::from(0),
                        node: Node::Statement(StmtId::from(0)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(1),
                parent: Some(ScopeId::from(0)),
                children: vec![],
                symbols: vec![(
                    ast.identifier_id("n"),
                    Symbol {
                        scope_id: ScopeId::from(1),
                        node: Node::Identifier(Identifier::new(
                            ast.identifier_id("n"),
                            Span::new(1, 7, 6, 1),
                        )),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
        ];

        assert_eq!(table.scopes, expected);
    }

    #[test]
    fn top_level_function_with_used_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { n; }"))
            .parse()
            .expect("source is valid");

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = vec![
            Scope {
                id: ScopeId::from(0),
                parent: None,
                children: vec![ScopeId::from(1)],
                symbols: vec![(
                    ast.identifier_id("f"),
                    Symbol {
                        scope_id: ScopeId::from(0),
                        node: Node::Statement(StmtId::from(1)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(1),
                parent: Some(ScopeId::from(0)),
                children: vec![],
                symbols: vec![(
                    ast.identifier_id("n"),
                    Symbol {
                        scope_id: ScopeId::from(1),
                        node: Node::Identifier(Identifier::new(
                            ast.identifier_id("n"),
                            Span::new(1, 7, 6, 1),
                        )),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
        ];

        assert_eq!(table.scopes, expected);
    }

    #[test]
    fn top_level_function_with_variable() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { let m = 0; }"))
            .parse()
            .expect("source is valid");

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = vec![
            Scope {
                id: ScopeId::from(0),
                parent: None,
                children: vec![ScopeId::from(1)],
                symbols: vec![(
                    ast.identifier_id("f"),
                    Symbol {
                        scope_id: ScopeId::from(0),
                        node: Node::Statement(StmtId::from(1)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(1),
                parent: Some(ScopeId::from(0)),
                children: vec![ScopeId::from(2)],
                symbols: vec![(
                    ast.identifier_id("n"),
                    Symbol {
                        scope_id: ScopeId::from(1),
                        node: Node::Identifier(Identifier::new(
                            ast.identifier_id("n"),
                            Span::new(1, 7, 6, 1),
                        )),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(2),
                parent: Some(ScopeId::from(1)),
                children: vec![],
                symbols: vec![(
                    ast.identifier_id("m"),
                    Symbol {
                        scope_id: ScopeId::from(2),
                        node: Node::Statement(StmtId::from(0)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
        ];

        assert_eq!(table.scopes, expected);
    }

    #[test]
    fn top_level_function_with_redefined_parameter() {
        let mut ast = Parser::new(Lexer::new("let f(n) = { let n = 0; }"))
            .parse()
            .expect("source is valid");

        let table = SymbolTableGen::new(&mut ast).build_table();

        let expected = vec![
            Scope {
                id: ScopeId::from(0),
                parent: None,
                children: vec![ScopeId::from(1)],
                symbols: vec![(
                    ast.identifier_id("f"),
                    Symbol {
                        scope_id: ScopeId::from(0),
                        node: Node::Statement(StmtId::from(1)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(1),
                parent: Some(ScopeId::from(0)),
                children: vec![ScopeId::from(2)],
                symbols: vec![(
                    ast.identifier_id("n"),
                    Symbol {
                        scope_id: ScopeId::from(1),
                        node: Node::Identifier(Identifier::new(
                            ast.identifier_id("n"),
                            Span::new(1, 7, 6, 1),
                        )),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
            Scope {
                id: ScopeId::from(2),
                parent: Some(ScopeId::from(1)),
                children: vec![],
                symbols: vec![(
                    ast.identifier_id("n"),
                    Symbol {
                        scope_id: ScopeId::from(2),
                        node: Node::Statement(StmtId::from(0)),
                    },
                )]
                .into_iter()
                .collect::<HashMap<IdentId, Symbol>>(),
            },
        ];

        assert_eq!(table.scopes, expected);
    }

    #[test]
    fn find_in_scope() {
        let mut ast = Parser::new(Lexer::new(
            "let f(n) = { let m = 0; let p = 0; let p = n + m; let q = p; }",
        ))
        .parse()
        .expect("source is valid");

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
            Node::Statement(stmt) => {
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
            Node::Identifier(ident) => {
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
            Node::Statement(stmt) => {
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
            Node::Statement(stmt) => {
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
        .expect("source is valid");

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
                Node::Statement(stmt) => {
                    assert_eq!(ast.statement(stmt).span().start(), 41);
                }
                _ => panic!("statement expected"),
            }
            let symbol = table
                .find(ast.identifier_id("b"), scope_id)
                .expect("a is in scope");
            match symbol.node {
                Node::Statement(stmt) => {
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
                Node::Statement(stmt) => {
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
                Node::Statement(stmt) => {
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
        .expect("source is valid");

        let table = SymbolTableGen::new(&mut ast).build_table();

        {
            let stmt = ast.statement_id(37);
            let scope_id = ast.statement(stmt).scope().expect("scope exists");
            let symbol = table
                .find(ast.identifier_id("a"), scope_id)
                .expect("a is in scope");
            match symbol.node {
                Node::Statement(stmt) => {
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
