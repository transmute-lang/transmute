use transmute_ast::expression::{Expression, ExpressionKind, Target};
use transmute_ast::statement::{RetMode, Statement, StatementKind};
use transmute_core::ids::{ExprId, StmtId};
use transmute_core::vec_map::VecMap;

#[derive(Default)]
pub struct ImplicitRetResolver {
    statements: VecMap<StmtId, Statement>,
    expressions: VecMap<ExprId, Expression>,
}

pub struct Output {
    pub statements: VecMap<StmtId, Statement>,
    pub expressions: VecMap<ExprId, Expression>,
}

impl ImplicitRetResolver {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn resolve(
        mut self,
        root_statement: StmtId,
        mut statements: VecMap<StmtId, Statement>,
        mut expressions: VecMap<ExprId, Expression>,
    ) -> Output {
        self.statements.resize(statements.len());
        self.expressions.resize(expressions.len());

        #[cfg(debug_assertions)]
        let (initial_statements_len, initial_expressions_len) =
            (statements.len(), expressions.len());

        let statement = statements.remove(root_statement).unwrap();
        self.visit_statement(
            &mut statements,
            &mut expressions,
            statement,
            0,
            false,
            false,
        );

        // we may have skipped the visit of statements or expressions due to the fact that their
        // parent was unreachable, and thus its children were not visited... we transfer them now.
        statements.into_iter().for_each(|(stmt_id, stmt)| {
            self.statements.insert(stmt_id, stmt);
        });
        expressions.into_iter().for_each(|(expr_id, expr)| {
            self.expressions.insert(expr_id, expr);
        });

        #[cfg(debug_assertions)]
        {
            debug_assert!(self.statements.len() >= initial_statements_len);
            debug_assert!(!self.statements.has_holes());
            debug_assert!(self.expressions.len() >= initial_expressions_len);
            debug_assert!(!self.expressions.has_holes());
        }

        Output {
            statements: self.statements,
            expressions: self.expressions,
        }
    }

    /// returns true if all nested paths explicitly return
    /// the depth is used to know if the expression is the function's last expression
    fn visit_expression(
        &mut self,
        statements: &mut VecMap<StmtId, Statement>,
        expressions: &mut VecMap<ExprId, Expression>,
        expression: Expression,
        depth: usize,
        unreachable: bool,
    ) -> bool {
        if unreachable {
            // we don't visit unreachable expression, possibly missing implicit exit points. as the
            // expressions are not reachable anyway, we ar safe
            self.expressions.insert(expression.id, expression);
            return false;
        }

        match &expression.kind {
            ExpressionKind::Assignment(target, expr) => {
                let target_expression = match target {
                    Target::Direct(_) => None,
                    Target::Indirect(target) => Some(expressions.remove(*target).unwrap()),
                };

                let value_expression = expressions.remove(*expr).unwrap();

                self.expressions.insert(expression.id, expression);

                let target_expression_returns = target_expression
                    .map(|expression| {
                        self.visit_expression(
                            statements,
                            expressions,
                            expression,
                            depth + 1,
                            unreachable,
                        )
                    })
                    .unwrap_or(false);

                let value_expression_returns = self.visit_expression(
                    statements,
                    expressions,
                    value_expression,
                    depth + 1,
                    unreachable,
                );

                value_expression_returns || target_expression_returns
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let cond_expression = expressions.remove(*cond).unwrap();
                let condition_always_returns = self.visit_expression(
                    statements,
                    expressions,
                    cond_expression,
                    depth + 1,
                    unreachable,
                );

                let true_branch_expression = expressions.remove(*true_branch).unwrap();
                let false_branch_expression =
                    false_branch.map(|expr_id| expressions.remove(expr_id).unwrap());

                let branches_always_return = if condition_always_returns {
                    // not that not visiting the true branch and the false branch expression
                    // prevents us to find potential implicit exit points there, but since  the
                    // condition always returns anyway we're safe
                    self.expressions
                        .insert(true_branch_expression.id, true_branch_expression);

                    if let Some(false_branch_expression) = false_branch_expression {
                        self.expressions
                            .insert(false_branch_expression.id, false_branch_expression);
                    }

                    // we don't know whether both branches always return, and we don't care as the
                    // condition always returns anyway
                    false
                } else {
                    let true_branch_always_return = self.visit_expression(
                        statements,
                        expressions,
                        true_branch_expression,
                        depth + 1,
                        unreachable,
                    );
                    let false_branch_always_return = false_branch_expression
                        .map(|false_branch_expression| {
                            self.visit_expression(
                                statements,
                                expressions,
                                false_branch_expression,
                                depth + 1,
                                unreachable,
                            )
                        })
                        .unwrap_or(false);

                    true_branch_always_return && false_branch_always_return
                };

                self.expressions.insert(expression.id, expression);

                condition_always_returns || branches_always_return
            }
            ExpressionKind::Literal(_) => {
                self.expressions.insert(expression.id, expression);
                false
            }
            ExpressionKind::Binary(..) | ExpressionKind::Unary(..) => {
                panic!("operators must be converted to functions");
            }
            ExpressionKind::Access(expr_id, _) => {
                let target_expression = expressions.remove(*expr_id).unwrap();

                self.expressions.insert(expression.id, expression);

                self.visit_expression(
                    statements,
                    expressions,
                    target_expression,
                    depth + 1,
                    unreachable,
                )
            }
            ExpressionKind::FunctionCall(_, params) => {
                let mut some_param_always_returns = false;

                for param in params {
                    let param_expression = expressions.remove(*param).unwrap();
                    some_param_always_returns = some_param_always_returns
                        || self.visit_expression(
                            statements,
                            expressions,
                            param_expression,
                            depth + 1,
                            unreachable || some_param_always_returns,
                        );
                }

                self.expressions.insert(expression.id, expression);

                some_param_always_returns
            }
            ExpressionKind::While(cond, expr) => {
                let cond_expression = expressions.remove(*cond).unwrap();
                let condition_always_returns = self.visit_expression(
                    statements,
                    expressions,
                    cond_expression,
                    depth + 1,
                    unreachable,
                );

                let block_expression = expressions.remove(*expr).unwrap();

                let block_always_returns = if condition_always_returns {
                    // not that not visiting the block expression prevents us to find potential
                    // implicit exit points there, but since the condition always returns
                    // anyway we're safe
                    self.expressions
                        .insert(block_expression.id, block_expression);

                    // we don't know whether the body always return, and we don't care as the
                    // condition always returns anyway
                    false
                } else {
                    self.visit_expression(
                        statements,
                        expressions,
                        block_expression,
                        depth + 1,
                        unreachable || condition_always_returns,
                    )
                };

                self.expressions.insert(expression.id, expression);

                condition_always_returns || block_always_returns
            }
            ExpressionKind::Block(stmts) if stmts.is_empty() => {
                if depth > 0 {
                    // we're not the root block of a function, we don't want to insert an implicit
                    // return. moreover, as the block is empty, it cannot always return. hence, we
                    // just insert the expression, and return `false`...

                    self.expressions.insert(expression.id, expression);

                    return false;
                }

                let stmt_id = self.statements.next_index();

                self.statements.push(Statement::new(
                    stmt_id,
                    StatementKind::Ret(None, RetMode::Implicit),
                    expression.span.clone(),
                ));

                self.expressions.insert(
                    expression.id,
                    Expression {
                        id: expression.id,
                        kind: ExpressionKind::Block(vec![stmt_id]),
                        span: expression.span,
                    },
                );

                true
            }
            ExpressionKind::Block(stmts) => {
                let stmts_len = stmts.len();
                let mut ret = false;
                for (i, stmt) in stmts.iter().enumerate() {
                    let last_statement = depth == 0 && i == stmts_len - 1 && !unreachable;

                    let statement = statements.remove(*stmt).unwrap();
                    if self.visit_statement(
                        statements,
                        expressions,
                        statement,
                        depth,
                        unreachable || ret,
                        last_statement,
                    ) {
                        ret = true;
                    }
                }

                if depth == 0 && !ret {
                    let stmt_id = self.statements.next_index();
                    self.statements.insert(
                        stmt_id,
                        Statement {
                            id: stmt_id,
                            kind: StatementKind::Ret(None, RetMode::Implicit),
                            // todo:ux can we do better?
                            span: Default::default(),
                        },
                    );

                    let mut stmts = stmts.clone();
                    stmts.push(stmt_id);

                    self.expressions.insert(
                        expression.id,
                        Expression {
                            id: expression.id,
                            kind: ExpressionKind::Block(stmts),
                            span: expression.span,
                        },
                    );
                } else {
                    self.expressions.insert(expression.id, expression);
                }

                ret
            }
            ExpressionKind::StructInstantiation(_, fields) => {
                let mut always_return = false;
                for (_, expr_id) in fields {
                    let field_expression = expressions.remove(*expr_id).unwrap();

                    let expression_returns = self.visit_expression(
                        statements,
                        expressions,
                        field_expression,
                        depth + 1,
                        unreachable || always_return,
                    );

                    always_return = always_return || expression_returns;
                }

                self.expressions.insert(expression.id, expression);

                always_return
            }
            ExpressionKind::ArrayInstantiation(values) => {
                let mut always_return = false;
                for expr_id in values {
                    let value_expression = expressions.remove(*expr_id).unwrap();

                    let expression_returns = self.visit_expression(
                        statements,
                        expressions,
                        value_expression,
                        depth + 1,
                        unreachable || always_return,
                    );

                    always_return = always_return || expression_returns;
                }

                self.expressions.insert(expression.id, expression);

                always_return
            }
            ExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => {
                let expr = expressions.remove(*base_expr_id).unwrap();
                let mut always_return =
                    self.visit_expression(statements, expressions, expr, depth + 1, false);

                let index = expressions.remove(*index_expr_id).unwrap();
                always_return = always_return
                    || self.visit_expression(
                        statements,
                        expressions,
                        index,
                        depth + 1,
                        always_return,
                    );

                self.expressions.insert(expression.id, expression);

                always_return
            }
            ExpressionKind::Dummy => {
                panic!("should not compute exit points of an invalid source code")
            }
        }
    }

    /// returns true if all nested paths explicitly return
    fn visit_statement(
        &mut self,
        statements: &mut VecMap<StmtId, Statement>,
        expressions: &mut VecMap<ExprId, Expression>,
        statement: Statement,
        depth: usize,
        unreachable: bool,
        last: bool,
    ) -> bool {
        if unreachable {
            // we don't visit unreachable expression, possibly missing implicit exit points. as the
            // expressions are not reachable anyway, we are safe
            self.statements.insert(statement.id, statement);
            return false;
        }

        match &statement.kind {
            StatementKind::Expression(expr_id) => {
                let expression = expressions.remove(*expr_id).unwrap();
                let always_returns = self.visit_expression(
                    statements,
                    expressions,
                    expression,
                    depth + 1,
                    unreachable,
                );

                if last && !always_returns {
                    self.statements.insert(
                        statement.id,
                        Statement {
                            id: statement.id,
                            kind: StatementKind::Ret(Some(*expr_id), RetMode::Implicit),
                            span: statement.span,
                        },
                    );
                    true
                } else {
                    self.statements.insert(statement.id, statement);
                    always_returns
                }
            }
            StatementKind::Let(_, expr) => {
                let expression = expressions.remove(*expr).unwrap();

                self.statements.insert(statement.id, statement);

                self.visit_expression(statements, expressions, expression, depth + 1, unreachable)
            }
            StatementKind::Ret(Some(expr), _) => {
                let expr = expressions.remove(*expr).unwrap();
                self.visit_expression(statements, expressions, expr, depth + 1, unreachable);

                self.statements.insert(statement.id, statement);

                true
            }
            StatementKind::Ret(None, _) => {
                self.statements.insert(statement.id, statement);
                true
            }
            StatementKind::LetFn(_, _, _, _, expr) => {
                let expr = expressions.remove(*expr).unwrap();
                self.visit_expression(statements, expressions, expr, 0, unreachable);

                self.statements.insert(statement.id, statement);

                false
            }
            StatementKind::Struct(_, _, _)
            | StatementKind::Annotation(_)
            | StatementKind::Use(_) => {
                self.statements.insert(statement.id, statement);
                false
            }
            StatementKind::Namespace(_, _, stmts) => {
                for stmt in stmts {
                    let statement = statements.remove(*stmt).unwrap();
                    self.visit_statement(statements, expressions, statement, 0, false, false);
                }
                self.statements.insert(statement.id, statement);
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::pretty_print::Options;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;

    macro_rules! t {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit = CompilationUnit::default();

                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), $src),
                )
                .parse();
                let mut ast = compilation_unit.into_ast().unwrap();

                // move out of ast without taking owership
                let mut statements = VecMap::new();
                for k in ast.statements.keys().into_iter() {
                    statements.insert(k, ast.statements.remove(k).unwrap());
                }

                let mut expressions = VecMap::new();
                for k in ast.expressions.keys().into_iter() {
                    expressions.insert(k, ast.expressions.remove(k).unwrap());
                }

                let explicit_rets =
                    ImplicitRetResolver::new().resolve(ast.root, statements, expressions);

                let expressions = explicit_rets.expressions;
                let statements = explicit_rets.statements;

                // move back into the ast
                for s in statements.into_iter() {
                    ast.statements.insert(s.0, s.1);
                }
                for e in expressions.into_iter() {
                    ast.expressions.insert(e.0, e.1);
                }

                let mut w = String::new();
                let mut options = Options::default();
                options.display_implicit_ret = true;
                ast.pretty_print(&options, &mut w).unwrap();

                assert_snapshot!(w);
            }
        };
    }

    t!(
        explicit_return,
        r#"
            let f(): number = {
                ret 42;
            }
        "#
    );

    t!(
        explicit_void_return,
        r#"
            let f() = {
                ret;
            }
        "#
    );

    t!(
        implicit_void_return,
        r#"
            let f() = {
            }
        "#
    );

    t!(
        implicit_return_simple,
        r#"
            let f(): number = {
                41;
                42;
            }
        "#
    );

    t!(
        implicit_return_if_full,
        r#"
            let f(): number = {
                if c {
                    42;
                }
                else {
                    43;
                }
            }
        "#
    );

    t!(
        implicit_return_if_full_with_explicit,
        r#"
            let f(): number = {
                if c {
                    ret 42;
                }
                else {
                    43;
                }
            }
        "#
    );

    t!(
        implicit_return_if,
        r#"
            let f(): number = {
                if c {
                    42;
                }
                43;
            }
        "#
    );

    t!(
        implicit_return_struct,
        r#"
            struct S { x: number, y: number }
            let f(): number = {
                S {
                    x: if true { ret 1; },
                    y: 1
                };
            }
        "#
    );

    t!(
        nested_function,
        r#"
            let f() {
                let g() {
                    true;
                };
                1;
            }
        "#
    );

    t!(
        while_condition_returns,
        "while if true { ret 42; } else { ret 43; } {}"
    );

    t!(
        if_condition_returns,
        "if if true { ret 42; } else { ret 43; } {}"
    );

    t!(
        struct_access,
        "struct S { field: number } let s = S { field: 1 }; s.field = false;"
    );

    t!(
        implicit_return_after_statement,
        "let f(n: number) { let a = 1; }"
    );

    t!(if_empty_branches, "let f() = { if true { } else { }; }");

    t!(while_empty_branches, "let f() = { while true { }; }");

    t!(
        array_value_always_ret,
        "let f(): number { let a = [1, if true { ret 2; } else { ret 3; }, 4]; 5; }"
    );
    t!(array, "let f(): number { let a = [1, 2, 4]; 5; }");

    t!(array_access_no_ret, "let f() { a[1]; }");
    t!(
        array_access_ret,
        "let f() { a[ if true { ret 1; } else { ret 2; } ]; }"
    );
    t!(namespace, "namespace name { let f(): number { 1; } }");
}
