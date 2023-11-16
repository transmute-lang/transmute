use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, IdentRefId, ScopeId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::StatementKind;
use crate::ast::{Ast, Visitor};
use crate::error::Diagnostics;
use crate::symbol_table::SymbolTable;

pub struct Resolver<'a> {
    ast: Ast,
    symbol_table: &'a SymbolTable,
    diagnostics: Diagnostics,
}

impl<'a> Resolver<'a> {
    pub fn new(ast: Ast, symbol_table: &'a SymbolTable) -> Self {
        Self {
            ast,
            symbol_table,
            diagnostics: Default::default(),
        }
    }

    pub fn resolve_symbols(mut self) -> (Ast, Diagnostics) {
        #[allow(clippy::unnecessary_to_owned)]
        for stmt in self.ast.statements().to_vec() {
            self.visit_statement(stmt);
        }

        (self.ast, self.diagnostics)
    }
}

impl<'a> Resolver<'a> {
    fn resolve(&mut self, ident: IdentRefId, scope: ScopeId) {
        let ident_ref = self.ast.identifier_ref(ident);
        let ident = ident_ref.ident().id();
        let symbol = self.symbol_table.find(ident, scope);
        match symbol {
            None => self.diagnostics.report_err(
                format!("'{}' not in scope", self.ast.identifier(ident),),
                ident_ref.ident().span().clone(),
                (file!(), line!()),
            ),
            Some(symbol) => {
                let mut ident_ref = ident_ref.clone();
                ident_ref.set_symbol_id(symbol.id());
                self.ast.replace_identifier_ref(ident_ref);
            }
        }
    }
}

impl<'a> Visitor<()> for Resolver<'a> {
    fn visit_statement(&mut self, stmt: StmtId) {
        let stmt = self.ast.statement(stmt);
        match stmt.kind() {
            StatementKind::Expression(expr)
            | StatementKind::Let(_, expr)
            | StatementKind::Ret(expr)
            | StatementKind::LetFn(_, _, expr) => self.visit_expression(*expr),
        }
    }

    fn visit_expression(&mut self, expr: ExprId) {
        let expr = self.ast.expression(expr);
        let scope = expr.scope().expect("expression scope exists");

        match expr.kind() {
            ExpressionKind::Assignment(ident, expr) => {
                let expr = *expr;

                self.resolve(*ident, scope);
                self.visit_expression(expr);
            }
            ExpressionKind::If(cond, true_expr, false_expr) => {
                let true_expr = *true_expr;
                let false_expr = *false_expr;

                self.visit_expression(*cond);
                self.visit_expression(true_expr);
                if let Some(false_expr) = false_expr {
                    self.visit_expression(false_expr);
                }
            }
            ExpressionKind::Literal(literal) => {
                if let LiteralKind::Identifier(ident) = literal.kind() {
                    self.resolve(*ident, scope);
                }
            }
            ExpressionKind::Binary(left, _, right) => {
                let right = *right;

                self.visit_expression(*left);
                self.visit_expression(right);
            }
            ExpressionKind::FunctionCall(_, exprs) => {
                // todo find ident node
                #[allow(clippy::unnecessary_to_owned)]
                for expr in exprs.to_vec() {
                    self.visit_expression(expr)
                }
            }
            ExpressionKind::Unary(_, expr) => {
                self.visit_expression(*expr);
            }
            ExpressionKind::While(cond, expr) => {
                let expr = *expr;

                self.visit_expression(*cond);
                self.visit_expression(expr)
            }
            ExpressionKind::Block(stmts) =>
            {
                #[allow(clippy::unnecessary_to_owned)]
                for stmt in stmts.to_vec() {
                    self.visit_statement(stmt);
                }
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

#[cfg(test)]
mod tests {
    use crate::error::Diagnostics;
    use crate::lexer::{Lexer, Span};
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use crate::symbol_table::{Node, SymbolTableGen};

    #[test]
    fn resolve_ref_to_parameter() {
        let mut ast = Parser::new(Lexer::new("let x(n) = { n; }")).parse().0;
        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = Resolver::new(ast, &symbol_table).resolve_symbols();

        assert!(diagnostics.is_empty());

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(13))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::Parameter(ident) => {
                assert_eq!(ident.span(), &Span::new(1, 7, 6, 1));
            }
            _ => panic!("expected parameter node kind"),
        }
    }

    #[test]
    fn resolve_ref_to_let() {
        let mut ast = Parser::new(Lexer::new("let x() = { let n = 0; n; }"))
            .parse()
            .0;
        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = Resolver::new(ast, &symbol_table).resolve_symbols();

        assert!(diagnostics.is_empty());

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(23))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::LetStatement(stmt) => {
                assert_eq!(ast.statement(*stmt).span(), &Span::new(1, 13, 12, 10));
            }
            _ => panic!("expected let statement node kind"),
        }
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let mut ast = Parser::new(Lexer::new("let x(n) = { while true { ret n; } }"))
            .parse()
            .0;
        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = Resolver::new(ast, &symbol_table).resolve_symbols();

        assert!(diagnostics.is_empty());

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(30))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::Parameter(ident) => {
                assert_eq!(ident.span(), &Span::new(1, 7, 6, 1));
            }
            _ => panic!("expected parameter node kind"),
        }
    }

    #[test]
    fn resolve_missing_def() {
        let mut ast = Parser::new(Lexer::new("let x() = { n; }")).parse().0;
        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (_, actual) = Resolver::new(ast, &symbol_table).resolve_symbols();

        let mut expected = Diagnostics::default();
        expected.report_err("'n' not in scope", Span::new(1, 13, 12, 1), (file!(), 43));

        assert_eq!(actual, expected);
    }
}
