use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperatorKind, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind};
use crate::ast::{Ast, Visitor};
use itertools::Itertools;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct Interpreter<'a> {
    ast: &'a Ast,
    // todo merge functions and variables (needs ValueKind)
    functions: HashMap<&'a str, (&'a Vec<Identifier>, &'a Vec<Statement>)>,
    variables: Vec<HashMap<&'a str, Value>>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a Ast) -> Self {
        Self {
            ast,
            functions: Default::default(),
            variables: vec![HashMap::default()],
        }
    }
    pub fn start(&mut self) -> Value {
        self.visit_ast(self.ast)
    }
}

impl<'a> Visitor<'a, Value> for Interpreter<'a> {
    fn visit_ast(&mut self, ast: &'a Ast) -> Value {
        ast.statements()
            .iter()
            .take_while_inclusive(|s| !is_ret(s))
            .map(|s| self.visit_statement(s))
            .last()
            .unwrap_or_default()
    }

    fn visit_statement(&mut self, stmt: &'a Statement) -> Value {
        match stmt.kind() {
            StatementKind::Expression(e) => self.visit_expression(e),
            StatementKind::Let(ident, expr) => {
                let val = self.visit_expression(expr);
                self.variables
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.name(), val);
                Value::Void
            }
            StatementKind::LetFn(ident, params, statements) => {
                self.functions.insert(ident.name(), (params, statements));
                Value::Void // todo this is wrong
            }
            StatementKind::Ret(e) => self.visit_expression(e),
        }
    }

    fn visit_expression(&mut self, expr: &'a Expression) -> Value {
        match expr.kind() {
            ExpressionKind::Literal(n) => self.visit_literal(n),
            ExpressionKind::Binary(l, o, r) => {
                let l = self.visit_expression(l);
                let r = self.visit_expression(r);
                match o.kind() {
                    BinaryOperatorKind::Addition => match (&l, &r) {
                        (Value::Number(l), Value::Number(r)) => Value::Number(l + r),
                        _ => panic!("+ not supported on {}, {}", l, r),
                    },
                    BinaryOperatorKind::Equality => match (&l, &r) {
                        (Value::Number(l), Value::Number(r)) => Value::Boolean(l == r),
                        (Value::Boolean(l), Value::Boolean(r)) => Value::Boolean(l == r),
                        _ => panic!("- not supported on {}, {}", l, r),
                    },
                    BinaryOperatorKind::Subtraction => match (&l, &r) {
                        (Value::Number(l), Value::Number(r)) => Value::Number(l - r),
                        _ => panic!("- not supported on {}, {}", l, r),
                    },
                    BinaryOperatorKind::Multiplication => match (&l, &r) {
                        (Value::Number(l), Value::Number(r)) => Value::Number(l * r),
                        _ => panic!("* not supported on {}, {}", l, r),
                    },
                    BinaryOperatorKind::Division => match (&l, &r) {
                        (Value::Number(l), Value::Number(r)) => Value::Number(l / r),
                        _ => panic!("/ not supported on {}, {}", l, r),
                    },
                }
            }
            ExpressionKind::Unary(o, e) => {
                let e = self.visit_expression(e);
                match o.kind() {
                    UnaryOperatorKind::Minus => match e {
                        Value::Number(e) => Value::Number(-e),
                        v => panic!("- not supported on {}", v),
                    },
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
                    .collect::<HashMap<&str, Value>>();

                self.variables.push(env);

                let ret = statements
                    .iter()
                    .take_while_inclusive(|s| !is_ret(s))
                    .map(|s| self.visit_statement(s))
                    .last()
                    .unwrap_or_default();

                let _ = self.variables.pop();

                ret
            }
        }
    }

    fn visit_literal(&mut self, literal: &'a Literal) -> Value {
        match literal.kind() {
            LiteralKind::Number(n) => Value::Number(*n),
            LiteralKind::Identifier(ident) => {
                match self
                    .variables
                    .last_mut()
                    .expect("there is an env")
                    .get(ident.name())
                {
                    None => panic!("{ident} not in scope"),
                    Some(v) => v.clone(),
                }
            }
            LiteralKind::Boolean(b) => Value::Boolean(*b),
        }
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Value {
    Boolean(bool),
    Number(i64),
    #[default]
    Void,
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Boolean(b) => {
                write!(f, "{}", b)
            }
            Value::Number(n) => {
                write!(f, "{}", n)
            }
            Value::Void => {
                write!(f, "void")
            }
        }
    }
}

fn is_ret(s: &Statement) -> bool {
    matches!(s.kind(), &StatementKind::Ret(_))
}

#[cfg(test)]
mod tests {
    use crate::interpreter::Interpreter;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    macro_rules! eval {
        ($name:ident, $src:expr => $kind:ident($value:expr)) => {
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($src));
                let ast = parser.parse().expect("source is valid");

                let actual = Interpreter::new(&ast).start();

                assert_eq!(actual, super::Value::$kind($value))
            }
        };
        ($name:ident, $src:expr => $kind:ident) => {
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($src));
                let ast = parser.parse().expect("source is valid");

                let actual = Interpreter::new(&ast).start();

                assert_eq!(actual, super::Value::$kind)
            }
        };
    }

    eval!(simple_precedence_1, "2 + 20 * 2;" => Number(42));
    eval!(simple_precedence_2, "20 * 2 + 2;" => Number(42));
    eval!(parenthesis_precedence, "(20 + 1) * 2;" => Number(42));
    eval!(negative_number, "-1 + 43;" => Number(42));
    eval!(unary_operator_minus_number, "- 1 + 43;" => Number(42));
    eval!(binary_operator_minus, "43 - 1;" => Number(42));
    eval!(unary_operator_minus_negative_number, "--42;" => Number(42));
    eval!(division, "85 / 2;" => Number(42));
    eval!(let_stmt, "let forty_two = 42;" => Void);
    eval!(let_stmt_then_expression, "let forty = 2 * 20; forty + 2;" => Number(42));
    eval!(function, "let times_two(v) = v * 2;" => Void);
    eval!(function_call, "let times_two(v) = v * 2; times_two(21);" => Number(42));
    eval!(complex_function_call, "let plus_one_times_two(v) = { let res = v + 1; res * 2; } plus_one_times_two(20);" => Number(42));
    eval!(ret_function_call, "let times_two(v) = { 41; ret v * 2; 42; } times_two(21);" => Number(42));
    eval!(bool_true, "true;" => Boolean(true));
    eval!(bool_false, "false;" => Boolean(false));
    eval!(equality_numbers_eq, "42 == 42;" => Boolean(true));
    eval!(equality_numbers_neq, "42 == 41;" => Boolean(false));
    eval!(equality_bool_eq1, "true == true;" => Boolean(true));
    eval!(equality_bool_eq2, "false == false;" => Boolean(true));
    eval!(equality_bool_neq1, "true == false;" => Boolean(false));
    eval!(equality_bool_neq2, "false == true;" => Boolean(false));
}
