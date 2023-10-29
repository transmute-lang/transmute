use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperatorKind, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind};
use crate::ast::{Ast, Visitor};
use std::collections::HashMap;

pub struct Interpreter<'a> {
    ast: &'a Ast,
    // todo merge functions and variables (needs ValueKind)
    functions: HashMap<&'a str, (&'a Vec<Identifier>, &'a Vec<Statement>)>,
    variables: Vec<HashMap<&'a str, i64>>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a Ast) -> Self {
        Self {
            ast,
            functions: Default::default(),
            variables: vec![HashMap::default()],
        }
    }
    pub fn start(&mut self) -> i64 {
        self.visit_ast(self.ast)
    }
}

impl<'a> Visitor<'a, i64> for Interpreter<'a> {
    fn visit_ast(&mut self, ast: &'a Ast) -> i64 {
        ast.statements()
            .iter()
            .map(|s| self.visit_statement(s))
            .last()
            .unwrap_or_default()
    }

    fn visit_statement(&mut self, stmt: &'a Statement) -> i64 {
        match stmt.kind() {
            StatementKind::Expression(e) => self.visit_expression(e),
            StatementKind::Let(ident, expr) => {
                let val = self.visit_expression(expr);
                self.variables
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.name(), val);
                0 // todo this is wrong
            }
            StatementKind::LetFn(ident, params, statements) => {
                self.functions.insert(ident.name(), (params, statements));
                0 // todo this is wrong
            }
        }
    }

    fn visit_expression(&mut self, expr: &'a Expression) -> i64 {
        match expr.kind() {
            ExpressionKind::Literal(n) => self.visit_literal(n),
            ExpressionKind::Binary(l, o, r) => {
                let l = self.visit_expression(l);
                let r = self.visit_expression(r);
                match o.kind() {
                    BinaryOperatorKind::Addition => l + r,
                    BinaryOperatorKind::Subtraction => l - r,
                    BinaryOperatorKind::Multiplication => l * r,
                    BinaryOperatorKind::Division => l / r,
                }
            }
            ExpressionKind::Unary(o, e) => {
                let e = self.visit_expression(e);
                match o.kind() {
                    UnaryOperatorKind::Minus => -e,
                }
            }
            ExpressionKind::MethodCall(ident, arguments) => {
                let (parameters, statements) = match self.functions.get(ident.name()) {
                    Some(f) => *f,
                    None => panic!("{ident} not in scope"),
                };

                if parameters.len() != arguments.len() {
                    panic!("Parameters and provided arguments for {ident} differ in length: expected {}, provided {}",
                        parameters.len(),
                        arguments.len()
                    )
                }

                let env = parameters
                    .iter()
                    .zip(arguments.iter())
                    .map(|(ident, expr)| (ident.name(), self.visit_expression(expr)))
                    .collect::<HashMap<&str, i64>>();

                self.variables.push(env);

                let ret = statements
                    .iter()
                    .map(|s| self.visit_statement(s))
                    .last()
                    .unwrap_or_default();

                let _ = self.variables.pop();

                ret
            }
        }
    }

    fn visit_literal(&mut self, literal: &'a Literal) -> i64 {
        match literal.kind() {
            LiteralKind::Number(n) => *n,
            LiteralKind::Identifier(ident) => {
                // todo this is incorrect, no default value allowed
                match self
                    .variables
                    .last_mut()
                    .expect("there is an env")
                    .get(ident.name())
                {
                    None => panic!("{ident} not in scope"),
                    Some(v) => *v,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::Interpreter;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    macro_rules! eval {
        ($name:ident, $src:expr => $expected:expr) => {
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($src));
                let ast = parser.parse().expect("source is valid");

                let actual = Interpreter::new(&ast).start();

                assert_eq!($expected, actual)
            }
        };
    }

    eval!(simple_precedence_1, "2 + 20 * 2;" => 42);
    eval!(simple_precedence_2, "20 * 2 + 2;" => 42);
    eval!(parenthesis_precedence, "(20 + 1) * 2;" => 42);
    eval!(negative_number, "-1 + 43;" => 42);
    eval!(unary_operator_minus_number, "- 1 + 43;" => 42);
    eval!(binary_operator_minus, "43 - 1;" => 42);
    eval!(unary_operator_minus_negative_number, "--42;" => 42);
    eval!(division, "85 / 2;" => 42);
    eval!(let_stmt, "let forty_two = 42;" => 0); // fixme should be a 'none' value
    eval!(let_stmt_then_expression, "let forty = 2 * 20; forty + 2;" => 42);
    eval!(function, "let times_two = (v) -> v * 2;" => 0); // fixme should be a 'none' or a 'function' value value
    eval!(function_call, "let times_two = (v) -> v * 2; times_two(21);" => 42);
    eval!(complex_function_call, "let plus_one_times_two = (v) -> { let res = v + 1; res * 2; } plus_one_times_two(20);" => 42);
}
