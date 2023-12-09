use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, IdentId, ScopeId, StmtId, SymbolId};
use crate::ast::literal::Literal;
use crate::ast::statement::{Parameter, StatementKind};
use crate::ast::{Ast, Visitor};
use crate::natives::{Native, Natives};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

pub struct SymbolTableGen<'a> {
    ast: &'a mut Ast,
    symbols: Vec<Symbol>,
    scopes: Vec<Scope>,
    scopes_stack: Vec<ScopeId>,
}

impl<'a> SymbolTableGen<'a> {
    pub fn new(ast: &'a mut Ast, natives: Natives) -> Self {
        let scope = ScopeId::from(0);
        let mut me = Self {
            ast,
            symbols: vec![],
            scopes: vec![Scope::root(scope)],
            scopes_stack: vec![scope],
        };

        for native in natives.into_iter() {
            let ident = me.ast.identifier_id(native.name());
            me.insert(ident, SymbolKind::Native(native));
        }

        me.push_scope();
        me
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
        match self.scopes_stack.last() {
            None => panic!("popped the last scope"),
            Some(scope) => {
                if self.scopes[scope.id()].parent.is_none() {
                    panic!("current scope is the root scope");
                }
            }
        }
    }

    fn insert(&mut self, ident: IdentId, node: SymbolKind) {
        let scope_id = self.scopes_stack.last().expect("there is a current scope");
        let scope = self.scopes.get_mut(scope_id.id()).expect("scope exists");
        let symbol_id = SymbolId::from(self.symbols.len());
        let symbol = Symbol {
            id: symbol_id,
            scope_id: *scope_id,
            kind: node,
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
                self.insert(ident.id(), SymbolKind::LetStatement(stmt));
            }
            StatementKind::LetFn(ident, params, _, expr) => {
                self.insert(ident.id(), SymbolKind::LetFnStatement(stmt, params.len()));

                // todo make sure type exist (or in type checker?)

                {
                    self.push_scope();
                    for (index, param) in params.iter().enumerate() {
                        self.insert(
                            param.identifier().id(),
                            SymbolKind::Parameter(param.clone(), stmt, index),
                        );
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
    symbols: HashMap<IdentId, Vec<SymbolId>>,
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
        // todo make sure we dont insert the same symbol twice
        self.symbols.entry(identifier).or_default().push(symbol_id);
    }

    pub fn id(&self) -> ScopeId {
        self.id
    }

    pub fn parent(&self) -> Option<ScopeId> {
        self.parent
    }

    pub fn children(&self) -> &Vec<ScopeId> {
        &self.children
    }

    pub fn get(&self, identifier: IdentId) -> Option<Vec<SymbolId>> {
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

#[derive(Debug, PartialEq)]
pub struct Symbol {
    id: SymbolId,
    /// points to the scope where this symbol is defined
    scope_id: ScopeId,
    /// the AST node that defines that symbol
    kind: SymbolKind,
}

impl Symbol {
    pub fn id(&self) -> SymbolId {
        self.id
    }

    pub fn scope(&self) -> ScopeId {
        self.scope_id
    }

    pub fn kind(&self) -> &SymbolKind {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    LetStatement(StmtId),
    // usize is arity
    LetFnStatement(StmtId, usize),
    Parameter(/*todo delete*/ Parameter, StmtId, usize),
    Native(Native),
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

    pub fn find(&self, identifier: IdentId, scope: ScopeId) -> Option<&Symbol> {
        let scope = &self.scopes[scope.id()];
        if let Some(symbols) = scope.get(identifier) {
            if symbols.len() != 1 {
                // fixme: this does not work with eq(n, 0) for instance
                panic!("Expected 1 symbol. found {}", symbols.len());
            }
            Some(&self.symbols[symbols.first().unwrap().id()])
        } else if let Some(parent) = scope.parent {
            self.find(identifier, parent)
        } else {
            None
        }
    }

    pub fn find_with_arity(
        &self,
        identifier: IdentId,
        arity: usize,
        scope: ScopeId,
    ) -> Vec<SymbolId> {
        let scope = &self.scopes[scope.id()];
        match scope.get(identifier) {
            Some(s) => {
                let mut symbols = s
                    .iter()
                    .filter(|s| match &self.symbols[s.id()].kind {
                        SymbolKind::LetStatement(_) => false,
                        SymbolKind::LetFnStatement(_, a) => arity == *a,
                        SymbolKind::Parameter(_, _, _) => false,
                        SymbolKind::Native(native) => native.parameters().len() == arity,
                    })
                    .cloned()
                    .collect::<Vec<SymbolId>>();
                if let Some(parent) = scope.parent {
                    symbols.append(&mut self.find_with_arity(identifier, arity, parent));
                }
                symbols
            }
            None => {
                if let Some(parent) = scope.parent {
                    self.find_with_arity(identifier, arity, parent)
                } else {
                    vec![]
                }
            }
        }
    }

    pub fn symbols(&self) -> &Vec<Symbol> {
        &self.symbols
    }

    pub fn scopes(&self) -> &Vec<Scope> {
        &self.scopes
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id.id()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;
    use crate::type_check::Type;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

    #[test]
    fn top_level_function_with_parameter() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new("let f(n: number) = { }")).parse().0;
        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn top_level_function_with_used_parameter() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new("let f(n: number): number = { n; }"))
            .parse()
            .0;
        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn top_level_function_with_variable() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new("let f(n: number) = { let m = 0; }"))
            .parse()
            .0;

        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn top_level_function_with_redefined_parameter() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new("let f(n: number) = { let n = 0; }"))
            .parse()
            .0;

        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn find_in_scope() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new(
            "let f(n: number) = { let m = 0; let p = 0; let p = n + m; let q = p; }",
        ))
        .parse()
        .0;

        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize())
    }

    #[test]
    fn if_statement() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new(
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

        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn while_statement() {
        let natives = Natives::default();

        let ast = Parser::new(Lexer::new(
            "let x() = { while true { let a = 42; a; } let b = 42; }",
        ))
        .parse()
        .0;

        let mut ast = ast.merge(Into::<Ast>::into(&natives));

        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        assert_snapshot!(XmlWriter::new(&ast, &table).serialize());
    }

    #[test]
    fn find_with_arity_add() {
        let ast = Ast::default();
        let natives = Natives::default();
        let mut ast = ast.merge(Into::<Ast>::into(&natives));
        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        let add = ast.identifier_id("add");
        let symbols = table.find_with_arity(add, 2, ScopeId::from(0));
        assert_eq!(symbols.len(), 1);

        let symbol = table.symbol(*symbols.first().unwrap());
        match &symbol.kind {
            SymbolKind::Native(native) => {
                assert_eq!(native.parameters(), &vec![Type::Number, Type::Number]);
            }
            _ => panic!("expected native, got {:?}", symbol.kind),
        }
    }
    #[test]
    fn find_with_arity_eq() {
        let ast = Ast::default();
        let natives = Natives::default();
        let mut ast = ast.merge(Into::<Ast>::into(&natives));
        let table = SymbolTableGen::new(&mut ast, natives).build_table();

        let eq = ast.identifier_id("eq");
        let symbols = table.find_with_arity(eq, 2, ScopeId::from(0));
        assert_eq!(symbols.len(), 2);

        let mut params = symbols
            .iter()
            .map(|s| table.symbol(*s))
            .map(|s| match &s.kind {
                SymbolKind::Native(native) => native
                    .parameters()
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<String>>()
                    .join(","),
                _ => panic!("expected native, got {:?}", s.kind),
            })
            .collect::<Vec<String>>();
        params.sort();
        assert_eq!(
            params,
            vec!["boolean,boolean".to_string(), "number,number".to_string()]
        );
    }
}
