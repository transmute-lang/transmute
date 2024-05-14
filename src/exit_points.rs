use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, StmtId};
use crate::ast::statement::{RetMode, StatementKind};
use crate::ast::{Ast, WithoutImplicitRet};

pub struct ExitPoints<'a> {
    ast: &'a Ast<WithoutImplicitRet>,
    exit_points: Vec<ExitPoint>,
    unreachable: Vec<ExprId>,
}

impl<'a> ExitPoints<'a> {
    pub fn new(ast: &'a Ast<WithoutImplicitRet>) -> Self {
        Self {
            ast,
            exit_points: Default::default(),
            unreachable: Default::default(),
        }
    }

    pub fn exit_points(mut self, expr: ExprId) -> Vec<ExitPoint> {
        match self.ast.expression(expr).kind() {
            ExpressionKind::Block(_) => {}
            e => panic!("expected block got {:?}", e),
        };

        self.visit_expression(expr, 0, false);

        let mut exit_points = self
            .exit_points
            .into_iter()
            .filter(|e| {
                let e = match e {
                    ExitPoint::Explicit(e) => e,
                    ExitPoint::Implicit(e) => e,
                };
                !self.unreachable.contains(e)
            })
            .collect::<Vec<ExitPoint>>();
        exit_points.sort();
        exit_points.dedup();

        exit_points
    }

    fn visit_expression(&mut self, expr: ExprId, depth: usize, unreachable: bool) -> bool {
        if unreachable {
            self.unreachable.push(expr);
            return false;
        }

        let always_returns = match self.ast.expression(expr).kind() {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(*expr, depth + 1, unreachable)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let condition_always_returns = self.visit_expression(*cond, depth + 1, unreachable);

                let true_branch_always_return = self.visit_expression(
                    *true_branch,
                    depth + 1,
                    unreachable || condition_always_returns,
                );

                let false_branch_always_return = match false_branch {
                    None => false,
                    Some(false_branch) => self.visit_expression(
                        *false_branch,
                        depth + 1,
                        unreachable || condition_always_returns,
                    ),
                };

                condition_always_returns
                    || (true_branch_always_return && false_branch_always_return)
            }
            ExpressionKind::Literal(_) => false,
            ExpressionKind::Binary(left, _, right) => {
                let left_always_returns = self.visit_expression(*left, depth + 1, unreachable);
                let right_always_returns =
                    self.visit_expression(*right, depth + 1, unreachable || left_always_returns);
                left_always_returns || right_always_returns
            }
            ExpressionKind::FunctionCall(_, params) => {
                let mut some_param_always_returns = false;

                for param in params {
                    some_param_always_returns = some_param_always_returns
                        || self.visit_expression(
                            *param,
                            depth + 1,
                            unreachable || some_param_always_returns,
                        );
                }

                some_param_always_returns
            }
            ExpressionKind::Unary(_, expr) => self.visit_expression(*expr, depth + 1, unreachable),
            ExpressionKind::While(cond, expr) => {
                let condition_always_returns = self.visit_expression(*cond, depth + 1, unreachable);
                let while_always_returns = self.visit_expression(
                    *expr,
                    depth + 1,
                    unreachable || condition_always_returns,
                );
                condition_always_returns || while_always_returns
            }
            ExpressionKind::Block(stmts) => {
                let mut ret = false;
                for stmt in stmts.iter() {
                    if self.visit_statement(*stmt, depth, unreachable || ret) {
                        ret = true;
                    }
                }
                ret
            }
            ExpressionKind::Dummy => {
                panic!("should not compute exit points of an invalid source code")
            }
        };

        always_returns
    }

    fn visit_statement(&mut self, stmt: StmtId, depth: usize, unreachable: bool) -> bool {
        match self.ast.statement(stmt).kind() {
            StatementKind::Expression(expr) => self.visit_expression(*expr, depth + 1, unreachable),
            StatementKind::Let(_, expr) => self.visit_expression(*expr, depth + 1, unreachable),
            StatementKind::Ret(expr, mode) => {
                match mode {
                    RetMode::Explicit => {
                        self.exit_points.push(ExitPoint::Explicit(*expr));
                    }
                    RetMode::Implicit => {
                        self.exit_points.push(ExitPoint::Implicit(*expr));
                    }
                }
                self.visit_expression(*expr, depth + 1, unreachable);
                true
            }
            StatementKind::LetFn(_, _, _, expr) => {
                self.visit_expression(*expr, depth + 1, unreachable);
                false
            }
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExitPoint {
    Explicit(ExprId),
    Implicit(ExprId),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::desugar::ImplicitRet;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    #[test]
    fn single_explicit_exit_point() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                ret 42;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(1);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let expected = vec![ExitPoint::Explicit(ExprId::from(0))];

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_1() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = if true {
                ret 42;
            }
            else {
                ret 43;
            };"#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(6);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_2() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                if true {
                    ret 42;
                }
                else {
                    ret 43;
                }
            }"#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(6);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_masking_later_exit_points() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                if true {
                    ret 42;
                }
                else {
                    ret 43;
                }
                ret 44;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(7);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_if_condition() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                if if true { ret 42; } else { ret 43; } {
                    ret 44;
                }
                ret 45;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(10);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_while() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                while true {
                    ret 42;
                }
                ret 43;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(5);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![ExitPoint::Explicit(ExprId::from(1))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn while_never_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                while true { }
                ret 42;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(4);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![ExitPoint::Explicit(ExprId::from(3))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_while_condition() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let f() = {
                while if true { ret 42; } else { ret 43; } {
                    ret 44;
                }
                ret 45;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(10);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn assignment_always_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let x = 0;
                x = if true { ret 42; } else { ret 43; };
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(8);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(2)),
            ExitPoint::Explicit(ExprId::from(4)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn left_binary_always_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = if true { ret 42; } else { ret 43; }
                      + if false { ret 44; } else { ret 45; };
                ret 46;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);
        let expr = ExprId::from(14);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn left_binary_sometimes_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = if true { 42; } else { ret 43; }
                      + if false { ret 44; } else { ret 45; };
                ret 46;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(14);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(3)),
            ExitPoint::Explicit(ExprId::from(7)),
            ExitPoint::Explicit(ExprId::from(9)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn right_binary_always_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = 42 + if false { ret 43; } else { ret 44; };
                ret 45;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(9);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(2)),
            ExitPoint::Explicit(ExprId::from(4)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn binary_never_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = 42 + 43;
                ret 44;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(4);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![ExitPoint::Explicit(ExprId::from(3))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn unary_always_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = - if true { ret 42; } else { ret 43; };
                ret 44;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(8);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_call_parameter_always_returns() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            r#"let x(a: number) = {
                x(if true { ret 42; } else { ret 43; });
                ret 44;
            }
            "#,
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{}", diagnostics);

        let ast = ImplicitRet::new().desugar(ast);

        let expr = ExprId::from(8);

        let actual = ExitPoints::new(&ast).exit_points(expr);
        let mut expected = vec![
            ExitPoint::Explicit(ExprId::from(1)),
            ExitPoint::Explicit(ExprId::from(3)),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }
}
