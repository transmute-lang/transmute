use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, IdentRefId, ScopeId, StmtId, SymbolId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::StatementKind;
use crate::ast::{Ast, Visitor};
use crate::error::Diagnostics;
use crate::exit_points::ExitPoints;
use crate::natives::Natives;
use crate::symbol_table::{Node, SymbolTable};
use std::fmt::{Display, Formatter};

pub struct TypeChecker<'a> {
    ast: Ast,
    table: &'a SymbolTable,
    // todo should maybe be part of the symbol table
    predefined: &'a Natives,
    types: Vec<Option<Res>>,
    diagnostics: Diagnostics,
}

impl<'a> TypeChecker<'a> {
    pub fn new(ast: Ast, table: &'a SymbolTable, predefined: &'a Natives) -> Self {
        let mut types = Vec::with_capacity(ast.expressions_count());
        for _ in 0..ast.expressions_count() {
            types.push(None);
        }

        Self {
            ast,
            table,
            predefined,
            types,
            diagnostics: Default::default(),
        }
    }

    pub fn check(mut self) -> (Ast, Diagnostics) {
        #[allow(clippy::unnecessary_to_owned)]
        for stmt in self.ast.statements().to_vec() {
            let _ = self.visit_statement(stmt);
        }
        (self.ast, self.diagnostics)
    }

    fn resolve(&mut self, ident: IdentRefId, scope: ScopeId) -> Option<SymbolId> {
        let ident_ref = self.ast.identifier_ref(ident);
        let ident = ident_ref.ident().id();
        let symbol = self.table.find(ident, scope);
        match symbol {
            None => {
                self.diagnostics.report_err(
                    format!("'{}' not in scope", self.ast.identifier(ident),),
                    ident_ref.ident().span().clone(),
                    (file!(), line!()),
                );
                None
            }
            Some(symbol) => {
                let mut ident_ref = ident_ref.clone();
                ident_ref.set_symbol_id(symbol.id());
                self.ast.replace_identifier_ref(ident_ref);
                Some(symbol.id())
            }
        }
    }
}

type Res = Result<Option<Type>, ()>;

impl Visitor<Res> for TypeChecker<'_> {
    fn visit_statement(&mut self, stmt_id: StmtId) -> Res {
        let stmt = self.ast.statement(stmt_id);

        match stmt.kind() {
            StatementKind::Expression(expr) => self.visit_expression(*expr),
            StatementKind::Let(_, expr) => {
                let expr = *expr;
                // fixme this is wrong, the let does not have a type, only the expr... but it's an
                //  acceptable proxy
                match self.visit_expression(expr) {
                    Ok(None) => {
                        let expr = self.ast.expression(expr);
                        self.diagnostics.report_err(
                            "Expected some type, got none",
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                        Err(())
                    }
                    t => t,
                }
            }
            StatementKind::Ret(expr) => {
                let _ = self.visit_expression(*expr);
                Ok(None)
            }
            StatementKind::LetFn(_, _, ty, expr) => {
                let ret_type = match ty {
                    None => Ok(Type::Void),
                    Some(ident) => match Type::try_from(self.ast.identifier(ident.id())) {
                        Ok(ty) => Ok(ty),
                        Err(e) => {
                            self.diagnostics.report_err(
                                e,
                                ty.as_ref().unwrap().span().clone(),
                                (file!(), line!()),
                            );
                            Err(())
                        }
                    },
                }?;

                let expr = *expr;
                let _ = self.visit_expression(expr);

                let exit_points = ExitPoints::new(&self.ast).exit_points(expr);
                if exit_points.is_empty() {
                    if ret_type != Type::Void {
                        let stmt = self.ast.statement(stmt_id);
                        self.diagnostics.report_err(
                            format!("Expected type {ret_type}, got void"),
                            stmt.span().clone(),
                            (file!(), line!()),
                        );
                    }
                } else {
                    for expr in exit_points {
                        match self.visit_expression(expr) {
                            Ok(Some(ty)) => {
                                if ty != ret_type {
                                    let expr = self.ast.expression(expr);
                                    self.diagnostics.report_err(
                                        format!("Expected type {ret_type}, got {ty}"),
                                        expr.span().clone(),
                                        (file!(), line!()),
                                    );
                                }
                            }
                            Ok(None) => panic!(),
                            Err(_) => {}
                        }
                    }
                }

                Ok(Some(Type::Function))
            }
        }
    }

    fn visit_expression(&mut self, expr_id: ExprId) -> Res {
        if let Some(t) = self.types[expr_id.id()] {
            return t;
        }

        let expr = self.ast.expression(expr_id);
        let scope = expr.scope().expect("expression scope exists");

        let t = match expr.kind() {
            ExpressionKind::Assignment(ident, expr) => {
                let expr = *expr;
                let ident = *ident;
                match self.resolve(ident, scope) {
                    Some(symbol) => {
                        let symbol = self.table.symbol(symbol);

                        let target_type = match symbol.node() {
                            Node::LetStatement(stmt) => self.visit_statement(*stmt),
                            Node::LetFnStatement(_) => {
                                panic!("cannot assign to a let fn");
                            }
                            Node::Parameter(_) => {
                                panic!("cannot assign to a parameter");
                            }
                        }?;

                        let expr_type = self.visit_expression(expr)?;

                        match (target_type, expr_type) {
                            (Some(ident_type), Some(expr_type)) if ident_type == expr_type => {
                                Ok(Some(ident_type))
                            }
                            (Some(ident_type), Some(expr_type)) => {
                                let expr = self.ast.expression(expr);
                                self.diagnostics.report_err(
                                    format!("Expected {ident_type}, got {expr_type}",),
                                    expr.span().clone(),
                                    (file!(), line!()),
                                );
                                Err(())
                            }
                            (Some(t), None) => {
                                let expr = self.ast.expression(expr);
                                self.diagnostics.report_err(
                                    format!("Expected {t}, got no type",),
                                    expr.span().clone(),
                                    (file!(), line!()),
                                );
                                Err(())
                            }
                            (None, _) => panic!("ident has no type"),
                        }
                    }
                    None => Err(()),
                }
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let true_branch = *true_branch;
                let false_branch = *false_branch;

                let cond = *cond;
                let condition_type = self.visit_expression(cond)?;

                match condition_type {
                    Some(Type::Boolean) => {
                        // all good
                    }
                    Some(t) => {
                        let expr = self.ast.expression(cond);
                        self.diagnostics.report_err(
                            format!("Expected boolean, got {t}"),
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                    }
                    None => {
                        let expr = self.ast.expression(cond);
                        self.diagnostics.report_err(
                            "Expected boolean, got no type",
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                    }
                }

                let true_type = self.visit_expression(true_branch)?;

                let false_type = false_branch
                    .map(|expr| self.visit_expression(expr))
                    .unwrap_or(Ok(Some(Type::Void)))?;

                match (true_type, false_type) {
                    (None, None) => Ok(None),
                    (None, Some(t)) | (Some(t), None) => Ok(Some(t)),
                    (Some(_), Some(Type::Void)) | (Some(Type::Void), Some(_)) => {
                        // todo: option<t>
                        Ok(Some(Type::Void))
                    }
                    (Some(tt), Some(ft)) if tt == ft => Ok(Some(tt)),
                    (Some(tt), Some(ft)) => {
                        let false_branch = self
                            .ast
                            .expression(false_branch.expect("false branch exists"));
                        self.diagnostics.report_err(
                            format!("Expected {tt}, got {ft}"),
                            false_branch.span().clone(),
                            (file!(), line!()),
                        );
                        Err(())
                    }
                }
            }
            ExpressionKind::While(cond, expr) => {
                let expr = *expr;

                let cond = *cond;
                let condition_type = self.visit_expression(cond)?;
                match condition_type {
                    Some(Type::Boolean) => {
                        // all good
                    }
                    Some(t) => {
                        let expr = self.ast.expression(cond);
                        self.diagnostics.report_err(
                            format!("Expected boolean, got {t}"),
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                    }
                    None => {
                        let expr = self.ast.expression(cond);
                        self.diagnostics.report_err(
                            "Expected boolean, got no type",
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                    }
                }

                self.visit_expression(expr)
            }
            ExpressionKind::Literal(literal) => match literal.kind() {
                LiteralKind::Boolean(_) => Ok(Some(Type::Boolean)),
                LiteralKind::Number(_) => Ok(Some(Type::Number)),
                LiteralKind::Identifier(ident_ref) => match self.resolve(*ident_ref, scope) {
                    Some(symbol) => {
                        let symbol = self.table.symbol(symbol);

                        match symbol.node() {
                            Node::LetStatement(stmt) => {
                                let stmt = self.ast.statement(*stmt);
                                match stmt.kind() {
                                    StatementKind::Let(_, expr) => self.visit_expression(*expr),
                                    _ => {
                                        panic!("expected let statement, got {:?}", stmt.kind())
                                    }
                                }
                            }
                            Node::LetFnStatement(_) => {
                                todo!()
                            }
                            Node::Parameter(p) => {
                                let ident = self.ast.identifier(p.ty().id());
                                match Type::try_from(ident) {
                                    Ok(ty) => Ok(Some(ty)),
                                    Err(e) => {
                                        self.diagnostics.report_err(
                                            e,
                                            p.span().clone(),
                                            (file!(), line!()),
                                        );
                                        Err(())
                                    }
                                }
                            }
                        }
                    }
                    None => Err(()),
                },
            },
            ExpressionKind::Unary(op, expr) => {
                let op = *op.kind();
                let expr = *expr;
                let ty = self.visit_expression(expr)?.unwrap_or(Type::Void);

                match self.predefined.find_fn(op.function_name(), vec![ty]) {
                    Some(predef) => Ok(Some(predef.return_type())),
                    None => {
                        let expr = self.ast.expression(expr);
                        self.diagnostics.report_err(
                            format!("Invalid type {ty} found for {op}"),
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                        Err(())
                    }
                }
            }
            ExpressionKind::Binary(left, op, right) => {
                let op = *op.kind();
                let left = *left;
                let right = *right;
                let left_type = self.visit_expression(left)?.unwrap_or(Type::Void);
                let right_type = self.visit_expression(right)?.unwrap_or(Type::Void);

                match self
                    .predefined
                    .find_fn(op.function_name(), vec![left_type, right_type])
                {
                    Some(predef) => Ok(Some(predef.return_type())),
                    None => {
                        self.diagnostics.report_err(
                            format!("Invalid types {left_type} and {right_type} found for {op}"),
                            self.ast
                                .expression(left)
                                .span()
                                .extend_to(self.ast.expression(right).span()),
                            (file!(), line!()),
                        );
                        Err(())
                    }
                }
            }
            ExpressionKind::FunctionCall(ident, exprs) => {
                let ident = *ident;

                #[allow(clippy::unnecessary_to_owned)]
                for expr in exprs.to_vec() {
                    let _ = self.visit_expression(expr);
                }

                match self.resolve(ident, scope) {
                    Some(symbol) => {
                        // todo use params to find function (overloads)
                        let ident = self.ast.identifier_ref(ident);

                        let ty = match self.table.symbol(symbol).node() {
                            Node::LetStatement(_) | Node::Parameter(_) => {
                                panic!(
                                    "'{}' is not a function",
                                    self.ast.identifier(ident.ident().id())
                                );
                            }
                            Node::LetFnStatement(stmt) => {
                                let stmt = self.ast.statement(*stmt);
                                match stmt.kind() {
                                    StatementKind::LetFn(_, _, ty, _) => ty.as_ref(),
                                    _ => panic!(),
                                }
                            }
                        };
                        match ty.map(|ty| self.ast.identifier(ty.id())) {
                            None => Ok(Some(Type::Void)),
                            Some(str) => match Type::try_from(str) {
                                Ok(t) => Ok(Some(t)),
                                Err(e) => {
                                    self.diagnostics.report_err(
                                        e,
                                        ty.unwrap().span().clone(),
                                        (file!(), line!()),
                                    );
                                    Err(())
                                }
                            },
                        }
                    }
                    None => Err(()),
                }
            }
            ExpressionKind::Block(stmt) => {
                let mut ty = Ok(Some(Type::Void));

                #[allow(clippy::unnecessary_to_owned)]
                for stmt in stmt.to_vec() {
                    let t = self.visit_statement(stmt);
                    match ty {
                        Ok(None) => {
                            // we keep the type of the expression only if we did not already see a
                            // ret
                        }
                        _ => ty = t,
                    }
                }

                ty
            }
            ExpressionKind::Dummy => {
                panic!("should not type check an invalid source code")
            }
        };

        self.types[expr_id.id()] = Some(t);
        t
    }

    fn visit_literal(&mut self, _literal: &Literal) -> Res {
        unimplemented!()
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    Boolean,
    Function,
    Number,
    Void,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function => write!(f, "function"),
            Type::Number => write!(f, "number"),
            Type::Void => write!(f, "void"),
        }
    }
}

impl TryFrom<&str> for Type {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "boolean" => Ok(Type::Boolean),
            "function" => Ok(Type::Function),
            "number" => Ok(Type::Number),
            "void" => Ok(Type::Void),
            &_ => Err(format!("'{}' is not a known type", value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::error::{Diagnostics, Level};
    use crate::lexer::{Lexer, Span};
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::symbol_table::{Node, SymbolTableGen};
    use crate::type_check::TypeChecker;

    #[test]
    fn resolve_ref_to_parameter() {
        let (mut ast, diagnostics) =
            Parser::new(Lexer::new("let x(n: number): number = { n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = TypeChecker::new(ast, &symbol_table, &Natives::default()).check();

        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(29))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::Parameter(ident) => {
                assert_eq!(ident.span(), &Span::new(1, 7, 6, 9));
            }
            _ => panic!("expected parameter node kind"),
        }
    }

    #[test]
    fn resolve_ref_to_let() {
        let (mut ast, diagnostics) =
            Parser::new(Lexer::new("let x(): number = { let n = 0; n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = TypeChecker::new(ast, &symbol_table, &Natives::default()).check();

        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(31))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::LetStatement(stmt) => {
                assert_eq!(ast.statement(*stmt).span(), &Span::new(1, 21, 20, 10));
            }
            _ => panic!("expected let statement node kind"),
        }
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let (mut ast, diagnostics) = Parser::new(Lexer::new("let x() = { } x();")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = TypeChecker::new(ast, &symbol_table, &Natives::default()).check();

        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(14))
            .symbol_id()
            .expect("symbol 'x' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::LetFnStatement(stmt) => {
                assert_eq!(ast.statement(*stmt).span(), &Span::new(1, 1, 0, 13));
            }
            _ => panic!("expected let statement node kind"),
        }
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let (mut ast, diagnostics) = Parser::new(Lexer::new(
            "let x(n: number): number = { while true { ret n; } }",
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (ast, diagnostics) = TypeChecker::new(ast, &symbol_table, &Natives::default()).check();

        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol = ast
            .identifier_ref(ast.identifier_ref_id(46))
            .symbol_id()
            .expect("symbol 'n' is resolved");
        match symbol_table.symbol(symbol).node() {
            Node::Parameter(ident) => {
                assert_eq!(ident.span(), &Span::new(1, 7, 6, 9));
            }
            _ => panic!("expected parameter node kind"),
        }
    }

    #[test]
    fn resolve_missing_def() {
        let (mut ast, diagnostics) = Parser::new(Lexer::new("let x() = { n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let symbol_table = SymbolTableGen::new(&mut ast).build_table();

        let (_ast, diagnostics) = TypeChecker::new(ast, &symbol_table, &Natives::default()).check();

        let mut expected = Diagnostics::default();
        expected.report_err("'n' not in scope", Span::new(1, 13, 12, 1), (file!(), 54));

        assert_eq!(diagnostics, expected);
    }

    macro_rules! test_type_error {
        ($name:ident, $src:expr, $error:expr, $span:expr) => {
            #[test]
            fn $name() {
                let (mut ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{}", diagnostics);
                let table = SymbolTableGen::new(&mut ast).build_table();
                let (_, actual_diagnostics) =
                    TypeChecker::new(ast, &table, &Natives::default()).check();

                let actual_diagnostics = actual_diagnostics
                    .iter()
                    .map(|d| (d.message(), d.span().clone(), d.level()))
                    .collect::<Vec<(&str, Span, Level)>>();

                let expected_diagnostics = vec![($error, $span, Level::Error)];

                assert_eq!(actual_diagnostics, expected_diagnostics);
            }
        };
    }

    macro_rules! test_type_ok {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let (mut ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{}", diagnostics);
                let table = SymbolTableGen::new(&mut ast).build_table();
                let (_, actual_diagnostics) =
                    TypeChecker::new(ast, &table, &Natives::default()).check();

                let actual_diagnostics = actual_diagnostics
                    .iter()
                    .map(|d| (d.message(), d.span().clone(), d.level()))
                    .collect::<Vec<(&str, Span, Level)>>();

                assert!(actual_diagnostics.is_empty(), "{:?}", actual_diagnostics);
            }
        };
    }

    test_type_error!(
        let_expr_type_is_void,
        "let x = if true { ret 42; } else { ret 43; };",
        "Expected some type, got none",
        Span::new(1, 9, 8, 36)
    );

    test_type_error!(
        if_expected_boolean_condition_got_number,
        "if 42 {}",
        "Expected boolean, got number",
        Span::new(1, 4, 3, 2)
    );
    test_type_ok!(if_expected_boolean_condition_got_boolean, "if true {}");
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_binary,
        "if 40 + 2 {}",
        "Expected boolean, got number",
        Span::new(1, 4, 3, 6)
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_unary,
        "if - 42 {}",
        "Expected boolean, got number",
        Span::new(1, 4, 3, 4)
    );
    test_type_error!(
        if_expected_boolean_condition_got_no_type,
        "if if true { ret 42; } else { ret 43; } {}",
        "Expected boolean, got no type",
        Span::new(1, 4, 3, 36)
    );
    test_type_ok!(
        if_expected_boolean_condition_got_boolean_expr,
        "if 42 > 40 {}"
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; if forty_two {}",
        "Expected boolean, got number",
        Span::new(1, 24, 23, 9)
    );
    test_type_ok!(
        if_expected_boolean_condition_got_boolean_identifier,
        "let t = true; if t {}"
    );
    test_type_error!(
        if_mismatch_branch_types,
        "if true { true; } else { 42; }",
        "Expected boolean, got number",
        Span::new(1, 24, 23, 7)
    );
    test_type_ok!(if_no_false_branch, "if true { 42; }");
    test_type_ok!(if_type, "let n = 0 + if true { 42; } else { 0; };");
    test_type_error!(
        if_expected_boolean_condition_got_number_in_else_if,
        "if true {} else if 42 {}",
        "Expected boolean, got number",
        Span::new(1, 20, 19, 2)
    );
    test_type_ok!(if_type_of_else_if, "if true { 42; } else if false { 0; }");
    test_type_error!(
        while_expected_boolean_condition_got_number,
        "while 42 {}",
        "Expected boolean, got number",
        Span::new(1, 7, 6, 2)
    );
    test_type_error!(
        while_expected_boolean_condition_got_no_type,
        "while if true { ret 42; } else { ret 43; } {}",
        "Expected boolean, got no type",
        Span::new(1, 7, 6, 36)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean,
        "while true {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_binary,
        "while 40 + 2 {}",
        "Expected boolean, got number",
        Span::new(1, 7, 6, 6)
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_unary,
        "while - 42 {}",
        "Expected boolean, got number",
        Span::new(1, 7, 6, 4)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_expr,
        "while 42 > 40 {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; while forty_two {}",
        "Expected boolean, got number",
        Span::new(1, 27, 26, 9)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_identifier,
        "let t = true; while t {}"
    );
    test_type_error!(
        assignment_wrong_type,
        "let forty_two = 42; forty_two = true;",
        "Expected number, got boolean",
        Span::new(1, 33, 32, 4)
    );
    test_type_ok!(
        assignment_correct_type,
        "let forty_two = 0; forty_two = 42;"
    );
    test_type_error!(
        assignment_wrong_type_from_function,
        "let forty_two = 42; let f(): boolean = true; forty_two = f();",
        "Expected number, got boolean",
        Span::new(1, 58, 57, 3)
    );
    test_type_error!(
        assignment_wrong_type_from_void_function,
        "let forty_two = 42; let f() = {} forty_two = f();",
        "Expected number, got void",
        Span::new(1, 46, 45, 3)
    );
    test_type_error!(
        assignment_always_returning_expr,
        "let forty_two = 42; forty_two = if true { ret 42; } else { ret 43; };",
        "Expected number, got no type",
        Span::new(1, 33, 32, 36)
    );
    test_type_ok!(
        assignment_correct_type_from_function,
        "let forty_two = 0; let f(): number = 42; forty_two = f();"
    );
    test_type_error!(
        function_invalid_return_type,
        "let f(): unknown = { }",
        "'unknown' is not a known type",
        Span::new(1, 10, 9, 7)
    );
    test_type_error!(
        function_wrong_return_type,
        "let f(): boolean = { true; 42; }",
        "Expected type boolean, got number",
        Span::new(1, 28, 27, 2)
    );
    test_type_error!(
        function_wrong_return_type_2,
        "let f(): boolean = { }",
        "Expected type boolean, got void",
        Span::new(1, 1, 0, 22)
    );
    test_type_error!(
        function_wrong_early_return_type,
        "let f(): number = { if false { ret false; } 42; }",
        "Expected type number, got boolean",
        Span::new(1, 36, 35, 5)
    );
    test_type_ok!(
        function_parameter_returned_correct_type,
        "let f(n: number): number = { n; }"
    );
    test_type_error!(
        function_parameter_returned_wrong_type,
        "let f(n: number): boolean = { n; }",
        "Expected type boolean, got number",
        Span::new(1, 31, 30, 1)
    );
    test_type_error!(
        function_parameter_updated_with_correct_type,
        "let f(n: number) = { let a = n + true; }",
        "Invalid types number and boolean found for +",
        Span::new(1, 30, 29, 8)
    );
    test_type_ok!(
        function_invalid_return_type_after_valid_return_type,
        "let f(n: number): number = { ret 41; ret true; }"
    );
    test_type_error!(
        unary_operator_invalid_type,
        "let n = - true;",
        "Invalid type boolean found for -",
        Span::new(1, 11, 10, 4)
    );
    test_type_error!(
        unary_operator_no_type,
        "let n = - if true { ret 42; } else { ret 43; };",
        "Invalid type void found for -",
        Span::new(1, 11, 10, 36)
    );
}
