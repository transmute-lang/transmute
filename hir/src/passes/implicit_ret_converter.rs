use transmute_ast::expression::{Expression, ExpressionKind};
use transmute_ast::statement::{RetMode, Statement, StatementKind};
use transmute_core::ids::{ExprId, StmtId};
use transmute_core::vec_map::VecMap;

pub struct ImplicitRetConverter {
    replacements: Vec<Statement>,
}

impl ImplicitRetConverter {
    pub fn new() -> Self {
        Self {
            replacements: Default::default(),
        }
    }

    pub fn convert(
        mut self,
        root_statements: &[StmtId],
        statements: &VecMap<StmtId, Statement>,
        expressions: &VecMap<ExprId, Expression>,
    ) -> Vec<Statement> {
        for expr_id in root_statements
            .iter()
            .filter_map(|stmt_id| match &statements[*stmt_id].kind {
                StatementKind::LetFn(_, _, _, expr_id) => Some(*expr_id),
                _ => None,
            })
            .filter(|expr_id| match &expressions[*expr_id].kind {
                ExpressionKind::Block(_) => true,
                e => panic!("expected block, got {:?}", e),
            })
        {
            self.visit_expression(statements, expressions, expr_id, 0, false);
        }

        self.replacements
    }

    /// returns true if all nested paths explicitly return
    /// the depth is used to know if the expression is the function's last expression
    fn visit_expression(
        &mut self,
        statements: &VecMap<StmtId, Statement>,
        expressions: &VecMap<ExprId, Expression>,
        expr: ExprId,
        depth: usize,
        unreachable: bool,
    ) -> bool {
        if unreachable {
            return false;
        }

        match &expressions[expr].kind {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(statements, expressions, *expr, depth + 1, unreachable)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let condition_always_returns =
                    self.visit_expression(statements, expressions, *cond, depth + 1, unreachable);

                let true_branch_always_return = self.visit_expression(
                    statements,
                    expressions,
                    *true_branch,
                    depth + 1,
                    unreachable || condition_always_returns,
                );

                let false_branch_always_return = match false_branch {
                    None => false,
                    Some(false_branch) => self.visit_expression(
                        statements,
                        expressions,
                        *false_branch,
                        depth + 1,
                        unreachable || condition_always_returns,
                    ),
                };

                condition_always_returns
                    || (true_branch_always_return && false_branch_always_return)
            }
            ExpressionKind::Literal(_) => false,
            ExpressionKind::Binary(..) | ExpressionKind::Unary(..) => {
                panic!("operators must be converted to functions");
            }
            ExpressionKind::Access(expr_id, _) => {
                self.visit_expression(statements, expressions, *expr_id, depth + 1, unreachable)
            }
            ExpressionKind::FunctionCall(_, params) => {
                let mut some_param_always_returns = false;

                for param in params {
                    some_param_always_returns = some_param_always_returns
                        || self.visit_expression(
                            statements,
                            expressions,
                            *param,
                            depth + 1,
                            unreachable || some_param_always_returns,
                        );
                }

                some_param_always_returns
            }
            ExpressionKind::While(cond, expr) => {
                let condition_always_returns =
                    self.visit_expression(statements, expressions, *cond, depth + 1, unreachable);
                let while_always_returns = self.visit_expression(
                    statements,
                    expressions,
                    *expr,
                    depth + 1,
                    unreachable || condition_always_returns,
                );
                condition_always_returns || while_always_returns
            }
            ExpressionKind::Block(stmts) => {
                let stmts_len = stmts.len();
                let mut ret = false;
                for (i, stmt) in stmts.iter().enumerate() {
                    let last_expr = depth == 0 && i == stmts_len - 1 && !unreachable;
                    if self.visit_statement(
                        statements,
                        expressions,
                        *stmt,
                        depth,
                        unreachable || ret,
                        last_expr,
                    ) {
                        ret = true;
                    }
                }
                ret
            }
            ExpressionKind::StructInstantiation(_, fields) => {
                let mut always_return = false;
                for (_, expr_id) in fields {
                    always_return = always_return
                        || self.visit_expression(
                            statements,
                            expressions,
                            *expr_id,
                            depth + 1,
                            unreachable || always_return,
                        );
                }
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
        statements: &VecMap<StmtId, Statement>,
        expressions: &VecMap<ExprId, Expression>,
        stmt_id: StmtId,
        depth: usize,
        unreachable: bool,
        last: bool,
    ) -> bool {
        match &statements[stmt_id].kind {
            StatementKind::Expression(expr) => {
                let expr = *expr;
                let always_returns =
                    self.visit_expression(statements, expressions, expr, depth + 1, unreachable);

                if last && !always_returns {
                    self.replacements.push(Statement::new(
                        stmt_id,
                        StatementKind::Ret(expr, RetMode::Implicit),
                        statements[stmt_id].span.clone(),
                    ));
                }

                always_returns
            }
            StatementKind::Let(_, expr) => {
                self.visit_expression(statements, expressions, *expr, depth + 1, unreachable)
            }
            StatementKind::Ret(expr, _) => {
                self.visit_expression(statements, expressions, *expr, depth + 1, unreachable);
                true
            }
            StatementKind::LetFn(_, _, _, expr) => {
                self.visit_expression(statements, expressions, *expr, 0, unreachable);
                false
            }
            StatementKind::Struct(_, _) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::passes::implicit_ret_converter::ImplicitRetConverter;
    use insta::assert_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::pretty_print::Options;

    macro_rules! t {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut ast = Parser::new(Lexer::new($src)).parse().unwrap();

                for new_statement in ImplicitRetConverter::new().convert(
                    &ast.roots,
                    &ast.statements,
                    &ast.expressions,
                ) {
                    ast.statements.insert(new_statement.id, new_statement);
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
}
