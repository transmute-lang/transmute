use transmute_ast::expression::{Expression, ExpressionKind};
use transmute_ast::statement::{RetMode, Statement, StatementKind};
use transmute_core::ids::{ExprId, StmtId};
use transmute_core::vec_map::VecMap;

pub struct ExitPointsResolver<'a> {
    expressions: &'a VecMap<ExprId, Expression>,
    statements: &'a VecMap<StmtId, Statement>,
}

#[derive(Default)]
struct Collected {
    exit_points: Vec<ExitPoint>,
    unreachable: Vec<ExprId>,
}

impl Collected {
    fn empty() -> Self {
        Self::default()
    }

    fn exit_point(exit_point: ExitPoint) -> Self {
        Self {
            exit_points: vec![exit_point],
            unreachable: Default::default(),
        }
    }

    fn unreachable(expr_id: ExprId) -> Self {
        Self {
            exit_points: Default::default(),
            unreachable: vec![expr_id],
        }
    }

    fn merge(&mut self, mut other: Self) {
        self.exit_points.append(&mut other.exit_points);
        self.unreachable.append(&mut other.unreachable);
    }

    fn finalize(self) -> Output {
        let mut exit_points = self
            .exit_points
            .into_iter()
            .filter(|e| match e.expr_id() {
                Some(e) => !self.unreachable.contains(&e),
                _ => true,
            })
            .collect::<Vec<ExitPoint>>();
        exit_points.sort();
        exit_points.dedup();

        let mut unreachable = self.unreachable;
        unreachable.dedup();

        Output {
            exit_points,
            unreachable,
        }
    }
}

#[derive(Debug)]
pub struct Output {
    pub exit_points: Vec<ExitPoint>,
    pub unreachable: Vec<ExprId>,
}

impl<'a> ExitPointsResolver<'a> {
    pub fn new(
        expressions: &'a VecMap<ExprId, Expression>,
        statements: &'a VecMap<StmtId, Statement>,
    ) -> Self {
        Self {
            expressions,
            statements,
        }
    }

    pub fn exit_points(&self, expr: ExprId) -> Output {
        if !matches!(&self.expressions[expr].kind, ExpressionKind::Block(_)) {
            panic!("expected block got {:?}", &self.expressions[expr].kind)
        }

        self.visit_expression(expr, 0, false).0.finalize()
    }

    /// return true is the expression returns
    fn visit_expression(&self, expr: ExprId, depth: usize, unreachable: bool) -> (Collected, bool) {
        if unreachable {
            return (Collected::unreachable(expr), false);
        }

        match &self.expressions[expr].kind {
            ExpressionKind::Assignment(_, expr) => {
                self.visit_expression(*expr, depth + 1, unreachable)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let true_branch = *true_branch;
                let false_branch = *false_branch;
                let (mut collected, condition_always_returns) =
                    self.visit_expression(*cond, depth + 1, unreachable);

                let (true_branch_collected, true_branch_always_return) = self.visit_expression(
                    true_branch,
                    depth + 1,
                    unreachable || condition_always_returns,
                );

                collected.merge(true_branch_collected);

                let (collected, false_branch_always_return) = match false_branch {
                    None => (collected, false),
                    Some(false_branch) => {
                        let (false_branch_collected, false_branch_always_return) = self
                            .visit_expression(
                                false_branch,
                                depth + 1,
                                unreachable || condition_always_returns,
                            );
                        collected.merge(false_branch_collected);
                        (collected, false_branch_always_return)
                    }
                };

                (
                    collected,
                    condition_always_returns
                        || (true_branch_always_return && false_branch_always_return),
                )
            }
            ExpressionKind::Literal(_) => (Collected::empty(), false),
            ExpressionKind::Access(expr_id, _) => {
                self.visit_expression(*expr_id, depth + 1, unreachable)
            }
            ExpressionKind::FunctionCall(_, params) => {
                let mut always_returns = false;
                let mut collected = Collected::default();

                for param in params {
                    let (param_collected, param_always_returns) =
                        self.visit_expression(*param, depth + 1, unreachable || always_returns);

                    always_returns = always_returns || param_always_returns;
                    collected.merge(param_collected);
                }

                (collected, always_returns)
            }
            ExpressionKind::Binary(..) | ExpressionKind::Unary(..) => {
                panic!("operators must be converted to functions")
            }
            ExpressionKind::While(cond, expr) => {
                let (mut collected, condition_always_returns) =
                    self.visit_expression(*cond, depth + 1, unreachable);

                let (expression_collected, while_always_returns) = self.visit_expression(
                    *expr,
                    depth + 1,
                    unreachable || condition_always_returns,
                );

                collected.merge(expression_collected);

                (collected, condition_always_returns || while_always_returns)
            }
            ExpressionKind::Block(stmts) => {
                let mut always_returns = false;
                let mut collected = Collected::default();

                for stmt in stmts.iter() {
                    let (stmt_collected, stmt_always_returns) =
                        self.visit_statement(*stmt, depth, unreachable || always_returns);

                    collected.merge(stmt_collected);
                    always_returns = always_returns || stmt_always_returns;
                }

                (collected, always_returns)
            }
            ExpressionKind::StructInstantiation(_, fields) => {
                let mut always_returns = false;
                let mut collected = Collected::default();

                for (_, field) in fields {
                    let (param_collected, param_always_returns) =
                        self.visit_expression(*field, depth + 1, unreachable || always_returns);

                    always_returns = always_returns || param_always_returns;
                    collected.merge(param_collected);
                }

                (collected, always_returns)
            }
            ExpressionKind::ArrayInstantiation(values) => {
                let mut always_returns = false;
                let mut collected = Collected::default();

                for value in values {
                    let (param_collected, param_always_returns) =
                        self.visit_expression(*value, depth + 1, unreachable || always_returns);

                    always_returns = always_returns || param_always_returns;
                    collected.merge(param_collected);
                }

                (collected, always_returns)
            }
            ExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => {
                let (mut collected, always_returns) =
                    self.visit_expression(*base_expr_id, depth + 1, false);

                let (index_collected, index_always_returns) =
                    self.visit_expression(*index_expr_id, depth + 1, unreachable || always_returns);

                let always_returns = always_returns || index_always_returns;
                collected.merge(index_collected);

                (collected, always_returns)
            }
            ExpressionKind::Dummy => {
                panic!("cannot compute exit points of an invalid source code")
            }
        }
    }

    fn visit_statement(
        &self,
        stmt_id: StmtId,
        depth: usize,
        unreachable: bool,
    ) -> (Collected, bool) {
        match &self.statements[stmt_id].kind {
            StatementKind::Expression(expr) => self.visit_expression(*expr, depth + 1, unreachable),
            StatementKind::Let(_, expr) => self.visit_expression(*expr, depth + 1, unreachable),
            StatementKind::Ret(expr, mode) => {
                let mut collected = match mode {
                    RetMode::Explicit => Collected::exit_point(ExitPoint::Explicit(*expr)),
                    RetMode::Implicit => Collected::exit_point(ExitPoint::Implicit(*expr)),
                };

                if let Some(expr) = expr {
                    let (expr_collected, _) = self.visit_expression(*expr, depth + 1, unreachable);
                    collected.merge(expr_collected);
                }

                (collected, true)
            }
            StatementKind::LetFn(_, _, _, _) => (Collected::default(), false),
            StatementKind::Struct(_, _) => (Collected::default(), false),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ExitPoint {
    Explicit(Option<ExprId>),
    Implicit(Option<ExprId>),
}

impl ExitPoint {
    fn expr_id(&self) -> Option<ExprId> {
        match self {
            ExitPoint::Explicit(e) | ExitPoint::Implicit(e) => *e,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_debug_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_core::ids::ExprId;

    #[test]
    fn single_explicit_exit_point() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                ret 42;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(1);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let expected = vec![ExitPoint::Explicit(Some(ExprId::from(0)))];

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_1() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = if true {
                ret 42;
            }
            else {
                ret 43;
            };"#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(6);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_2() {
        let ast = Parser::new(Lexer::new(
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
        .parse()
        .unwrap();

        let expr = ExprId::from(6);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn multiple_explicit_exit_points_masking_later_exit_points() {
        let ast = Parser::new(Lexer::new(
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
        .parse()
        .unwrap();

        let expr = ExprId::from(7);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_if_condition() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                if if true { ret 42; } else { ret 43; } {
                    ret 44;
                }
                ret 45;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(10);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_while() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                while true {
                    ret 42;
                }
                ret 43;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(5);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![ExitPoint::Explicit(Some(ExprId::from(1)))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn while_never_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                while true { }
                ret 42;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(4);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![ExitPoint::Explicit(Some(ExprId::from(3)))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn always_returns_from_while_condition() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() = {
                while if true { ret 42; } else { ret 43; } {
                    ret 44;
                }
                ret 45;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(10);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn assignment_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let x = 0;
                x = if true { ret 42; } else { ret 43; };
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(8);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(2))),
            ExitPoint::Explicit(Some(ExprId::from(4))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn left_binary_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = add(
                    if true { ret 42; } else { ret 43; },
                    if false { ret 44; } else { ret 45; }
                );
                ret 46;
            }
            "#,
        ))
        .parse()
        .unwrap();
        let expr = ExprId::from(14);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn left_binary_sometimes_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = add(
                    if true { 42; } else { ret 43; },
                    if false { ret 44; } else { ret 45; }
                );
                ret 46;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(14);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(3))),
            ExitPoint::Explicit(Some(ExprId::from(7))),
            ExitPoint::Explicit(Some(ExprId::from(9))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn right_binary_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = add(42, if false { ret 43; } else { ret 44; });
                ret 45;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(9);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(2))),
            ExitPoint::Explicit(Some(ExprId::from(4))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn binary_never_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = add(42, 43);
                ret 44;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(4);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![ExitPoint::Explicit(Some(ExprId::from(3)))];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn unary_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            let x() = {
                let a = minus(if true { ret 42; } else { ret 43; });
                ret 44;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(8);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_call_parameter_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"let x(a: number) = {
                x(if true { ret 42; } else { ret 43; });
                ret 44;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(8);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(1))),
            ExitPoint::Explicit(Some(ExprId::from(3))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn if_unreachable() {
        let ast = Parser::new(Lexer::new(
            r#"let x(a: number) = {
                if true {
                    ret 44;
                    43;
                }
                ret 44;
                42;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(7);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .unreachable;
        let mut expected = vec![ExprId::from(2), ExprId::from(6)];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn struct_always_returns() {
        let ast = Parser::new(Lexer::new(
            r#"
            struct S { x: number, y: number}
            let x(): number = {
                S {
                    x: if eq(1, 1) { ret 1; } else { ret 2; },
                    y: 1
                };
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(10);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .exit_points;
        let mut expected = vec![
            ExitPoint::Explicit(Some(ExprId::from(3))),
            ExitPoint::Explicit(Some(ExprId::from(5))),
        ];
        expected.sort();

        assert_eq!(actual, expected);
    }

    #[test]
    fn struct_unreachable() {
        let ast = Parser::new(Lexer::new(
            r#"
            struct S { x: number, y: number}
            let x(): number = {
                S {
                    x: if eq(1, 2) { ret 3; } else { ret 4; },
                    y: 5
                };
            }
            "#,
        ))
        .parse()
        .unwrap();

        let expr = ExprId::from(10);

        let actual = ExitPointsResolver::new(&ast.expressions, &ast.statements)
            .exit_points(expr)
            .unreachable;
        let mut expected = vec![ExprId::from(8)];
        expected.sort();

        assert_eq!(actual, expected);
    }

    // todo:refactoring rewrite other tests so they look like this one
    #[test]
    fn nested_function() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() {
                let g() {
                    ret true;
                };
                ret 1;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let block_exit_points = ast
            .expressions
            .iter()
            .filter_map(|(expr_id, expression)| {
                if matches!(expression.kind, ExpressionKind::Block(_)) {
                    Some((
                        expr_id,
                        ExitPointsResolver::new(&ast.expressions, &ast.statements)
                            .exit_points(expr_id),
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<(ExprId, Output)>>();

        assert_debug_snapshot!((ast, block_exit_points));
    }

    #[test]
    fn array_instantiation() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() {
                let a = [if true { ret 0; } else { ret 1; }];
                ret 2;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let block_exit_points = ast
            .expressions
            .iter()
            .filter_map(|(expr_id, expression)| {
                if matches!(expression.kind, ExpressionKind::Block(_)) {
                    Some((
                        expr_id,
                        ExitPointsResolver::new(&ast.expressions, &ast.statements)
                            .exit_points(expr_id),
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<(ExprId, Output)>>();

        assert_debug_snapshot!((ast, block_exit_points));
    }

    #[test]
    fn array_access() {
        let ast = Parser::new(Lexer::new(
            r#"
            let f() {
                let a = a[if true { ret 0; } else { ret 1; }];
                ret 2;
            }
            "#,
        ))
        .parse()
        .unwrap();

        let block_exit_points = ast
            .expressions
            .iter()
            .filter_map(|(expr_id, expression)| {
                if matches!(expression.kind, ExpressionKind::Block(_)) {
                    Some((
                        expr_id,
                        ExitPointsResolver::new(&ast.expressions, &ast.statements)
                            .exit_points(expr_id),
                    ))
                } else {
                    None
                }
            })
            .collect::<Vec<(ExprId, Output)>>();

        assert_debug_snapshot!((ast, block_exit_points));
    }
}
