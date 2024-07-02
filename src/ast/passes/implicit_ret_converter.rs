use crate::ast::expression::{ExpressionKind, Untyped};
use crate::ast::identifier_ref::Unbound;
use crate::ast::ids::{ExprId, StmtId};
use crate::ast::statement::{RetMode, Statement, StatementKind};
use crate::ast::{Ast, NoOperators};

pub struct ImplicitRetConverter {
    replacements: Vec<Statement<Untyped, Unbound>>,
}

impl ImplicitRetConverter {
    pub fn new() -> Self {
        Self {
            replacements: Default::default(),
        }
    }

    pub fn convert(
        mut self,
        ast: &Ast<NoOperators, Untyped, Unbound>,
    ) -> Vec<Statement<Untyped, Unbound>> {
        for expr in ast
            .root_statements()
            .iter()
            .filter_map(|stmt| match ast.statement(*stmt).kind() {
                StatementKind::LetFn(_, _, _, expr) => Some(*expr),
                _ => None,
            })
            .filter(|expr| match ast.expression(*expr).kind() {
                ExpressionKind::Block(_) => true,
                e => panic!("expected block, got {:?}", e),
            })
        {
            self.visit_expression(ast, expr, 0, false);
        }
        self.replacements
    }

    /// returns true if all nested paths explicitly return
    fn visit_expression(
        &mut self,
        ast: &Ast<NoOperators, Untyped, Unbound>,
        expr: ExprId,
        depth: usize,
        unreachable: bool,
    ) -> bool {
        if unreachable {
            return false;
        }

        match ast.expression(expr).kind() {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(ast, *expr, depth + 1, unreachable)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let condition_always_returns =
                    self.visit_expression(ast, *cond, depth + 1, unreachable);

                let true_branch_always_return = self.visit_expression(
                    ast,
                    *true_branch,
                    depth + 1,
                    unreachable || condition_always_returns,
                );

                let false_branch_always_return = match false_branch {
                    None => false,
                    Some(false_branch) => self.visit_expression(
                        ast,
                        *false_branch,
                        depth + 1,
                        unreachable || condition_always_returns,
                    ),
                };

                condition_always_returns
                    || (true_branch_always_return && false_branch_always_return)
            }
            ExpressionKind::Literal(_) => false,
            ExpressionKind::Binary(..) |  ExpressionKind::Unary(..)=> {
                panic!("operators must be converted to functions");

            }
            ExpressionKind::Access(expr_id, _) => {
                self.visit_expression(ast, *expr_id, depth + 1, unreachable)
            }
            ExpressionKind::FunctionCall(_, params) => {
                let mut some_param_always_returns = false;

                for param in params {
                    some_param_always_returns = some_param_always_returns
                        || self.visit_expression(
                            ast,
                            *param,
                            depth + 1,
                            unreachable || some_param_always_returns,
                        );
                }

                some_param_always_returns
            }
            ExpressionKind::While(cond, expr) => {
                let condition_always_returns =
                    self.visit_expression(ast, *cond, depth + 1, unreachable);
                let while_always_returns = self.visit_expression(
                    ast,
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
                    if self.visit_statement(ast, *stmt, depth, unreachable || ret, last_expr) {
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
                            ast,
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

    fn visit_statement(
        &mut self,
        ast: &Ast<NoOperators, Untyped, Unbound>,
        stmt: StmtId,
        depth: usize,
        unreachable: bool,
        last: bool,
    ) -> bool {
        match ast.statement(stmt).kind() {
            StatementKind::Expression(expr) => {
                let expr = *expr;
                let always_returns = self.visit_expression(ast, expr, depth + 1, unreachable);

                if last && !always_returns {
                    self.replacements.push(Statement::new(
                        stmt,
                        StatementKind::Ret(expr, RetMode::Implicit),
                        ast.statement(stmt).span().clone(),
                    ));
                }

                always_returns
            }
            StatementKind::Let(_, expr) => {
                self.visit_expression(ast, *expr, depth + 1, unreachable)
            }
            StatementKind::Ret(expr, _) => {
                self.visit_expression(ast, *expr, depth + 1, unreachable);
                true
            }
            StatementKind::LetFn(_, _, _, expr) => {
                self.visit_expression(ast, *expr, depth + 1, unreachable);
                false
            }
            StatementKind::Struct(_, _) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::output::pretty_print::Options;
    use crate::parser::Parser;
    use insta::assert_snapshot;

    macro_rules! t {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let ast = Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_operators()
                    .convert_implicit_ret();

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
}
