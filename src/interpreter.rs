use crate::ast::expression::{ExprId, ExpressionKind};
use crate::ast::identifier::{IdentId, Identifier};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperatorKind, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind, StmtId};
use crate::ast::{Ast, Visitor};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct Interpreter<'a> {
    ast: &'a Ast,
    // todo merge functions and variables (needs ValueKind)
    functions: HashMap<IdentId, (&'a Vec<Identifier>, &'a Vec<StmtId>)>,
    variables: Vec<HashMap<IdentId, Value>>,
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

impl<'a> Visitor<Value> for Interpreter<'a> {
    fn visit_ast(&mut self, ast: &Ast) -> Value {
        self.visit_statements(ast.statements())
    }

    fn visit_statement(&mut self, stmt: StmtId) -> Value {
        let stmt = self.ast.statement(&stmt);
        match stmt.kind() {
            StatementKind::Expression(e) => self.visit_expression(*e),
            StatementKind::Let(ident, expr) => {
                let val = self.visit_expression(*expr);
                self.variables
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.id(), val);
                Value::Void
            }
            StatementKind::LetFn(ident, params, statements) => {
                self.functions.insert(ident.id(), (params, statements));
                Value::Void // todo this is wrong
            }
            StatementKind::Ret(e) => self.visit_expression(*e),
        }
    }

    fn visit_expression(&mut self, expr: ExprId) -> Value {
        let expr = self.ast.expression(&expr);
        match expr.kind() {
            ExpressionKind::Literal(n) => self.visit_literal(n),
            ExpressionKind::Binary(l, o, r) => {
                let l = self.visit_expression(*l);
                let r = self.visit_expression(*r);

                match l {
                    Value::Boolean(b) => Value::Boolean(match o.kind() {
                        BinaryOperatorKind::Equality => b == r.try_to_bool(),
                        BinaryOperatorKind::NonEquality => b != r.try_to_bool(),
                        _ => panic!("{} not supported on bool", o.kind()),
                    }),
                    Value::Number(n) => match o.kind() {
                        BinaryOperatorKind::Addition => Value::Number(n + r.try_to_i64()),
                        BinaryOperatorKind::Division => Value::Number(n / r.try_to_i64()),
                        BinaryOperatorKind::Equality => Value::Boolean(n == r.try_to_i64()),
                        BinaryOperatorKind::GreaterThan => Value::Boolean(n > r.try_to_i64()),
                        BinaryOperatorKind::GreaterThanOrEqualTo => {
                            Value::Boolean(n >= r.try_to_i64())
                        }
                        BinaryOperatorKind::Multiplication => Value::Number(n * r.try_to_i64()),
                        BinaryOperatorKind::NonEquality => Value::Boolean(n != r.try_to_i64()),
                        BinaryOperatorKind::SmallerThan => Value::Boolean(n < r.try_to_i64()),
                        BinaryOperatorKind::SmallerThanOrEqualTo => {
                            Value::Boolean(n <= r.try_to_i64())
                        }
                        BinaryOperatorKind::Subtraction => Value::Number(n - r.try_to_i64()),
                    },
                    _ => panic!("{} not supported on {}", o.kind(), l),
                }
            }
            ExpressionKind::Unary(o, e) => {
                let e = self.visit_expression(*e);

                match e {
                    Value::Number(n) => Value::Number(match o.kind() {
                        UnaryOperatorKind::Minus => -n,
                    }),
                    _ => panic!("{} not supported on {}", o.kind(), e),
                }
            }
            ExpressionKind::FunctionCall(ident, arguments) => {
                let (parameters, statements) = match self.functions.get(&ident.id()) {
                    Some(f) => *f,
                    None => {
                        panic!("{} not in scope", self.ast.identifier(&ident.id()))
                    }
                };

                if parameters.len() != arguments.len() {
                    panic!("Parameters and provided arguments for {} differ in length: expected {}, provided {}",
                           self.ast.identifier(&ident.id()),
                           parameters.len(),
                           arguments.len()
                    )
                }

                let env = parameters
                    .iter()
                    .zip(arguments.iter())
                    .map(|(ident, expr)| (ident.id(), self.visit_expression(*expr)))
                    .collect::<HashMap<IdentId, Value>>();

                self.variables.push(env);

                let ret = self.visit_statements(statements).unwrap();

                let _ = self.variables.pop();

                ret
            }
            ExpressionKind::Assignment(ident, expr) => {
                // todo!()
                if !self
                    .variables
                    .last()
                    .expect("there is an env")
                    .contains_key(&ident.id())
                {
                    let ident = self.ast.identifier(&ident.id());
                    panic!("{ident} not in scope")
                }

                let val = self.visit_expression(*expr);

                self.variables
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.id(), val.clone());

                val
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let cond = self.visit_expression(*cond);
                let cond = match cond {
                    Value::Boolean(b) => b,
                    _ => panic!("condition is not a boolean"),
                };

                let statements = if cond { true_branch } else { false_branch };

                self.visit_statements(statements)
            }
            ExpressionKind::While(cond, statements) => {
                let mut ret = Value::Void;
                loop {
                    match self.visit_expression(*cond) {
                        Value::Boolean(false) => return ret,
                        Value::Boolean(true) => {}
                        _ => panic!("condition is not a boolean"),
                    };

                    ret = self.visit_statements(statements)
                }
            }
        }
    }

    fn visit_literal(&mut self, literal: &Literal) -> Value {
        match literal.kind() {
            LiteralKind::Number(n) => Value::Number(*n),
            LiteralKind::Identifier(ident) => {
                match self
                    .variables
                    .last_mut()
                    .expect("there is an env")
                    .get(&ident.id())
                {
                    None => {
                        panic!("{} not in scope", self.ast.identifier(&ident.id()))
                    }
                    Some(v) => v.clone(),
                }
            }
            LiteralKind::Boolean(b) => Value::Boolean(*b),
        }
    }
}

impl<'a> Interpreter<'a> {
    fn visit_statements(&mut self, statements: &Vec<StmtId>) -> Value {
        let mut value = Value::Void;

        for statement in statements {
            let statement = self.ast.statement(statement);
            if is_ret(statement) {
                return Value::RetVal(Box::new(self.visit_statement(statement.id())));
            }

            value = match self.visit_statement(statement.id()) {
                ret @ Value::RetVal(_) => return ret,
                v => v,
            }
        }

        value
    }
}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Value {
    Boolean(bool),
    Number(i64),
    /// a value, generated by a return statement
    RetVal(Box<Value>),
    #[default]
    Void,
}

impl Value {
    fn unwrap(self) -> Self {
        match self {
            Value::RetVal(v) => v.unwrap(),
            v => v,
        }
    }
}

impl Value {
    fn try_to_i64(self) -> i64 {
        match self {
            Value::Number(n) => n,
            _ => panic!("{} is not a number", self),
        }
    }

    fn try_to_bool(self) -> bool {
        match self {
            Value::Boolean(b) => b,
            _ => panic!("{} is not a bool", self),
        }
    }
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
            Value::RetVal(v) => {
                write!(f, "{}", v)
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
                let parser = Parser::new(Lexer::new($src));
                let ast = parser.parse().expect("source is valid");

                let actual = Interpreter::new(&ast).start();

                assert_eq!(actual, super::Value::$kind($value))
            }
        };
        ($name:ident, $src:expr => $kind:ident) => {
            #[test]
            fn $name() {
                let parser = Parser::new(Lexer::new($src));
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
    eval!(equality_numbers_eq_true, "42 == 42;" => Boolean(true));
    eval!(equality_numbers_eq_false, "42 == 41;" => Boolean(false));
    eval!(equality_numbers_neq_true, "42 != 42;" => Boolean(false));
    eval!(equality_numbers_neq_false, "42 != 42;" => Boolean(false));
    eval!(equality_booleans_eq_true, "true == true;" => Boolean(true));
    eval!(equality_booleans_eq_false, "true == false;" => Boolean(false));
    eval!(equality_booleans_neq_true, "true != true;" => Boolean(false));
    eval!(equality_booleans_neq_false, "true != false;" => Boolean(true));
    eval!(comaprison_1, "(42 > 42) != (42 >= 42);" => Boolean(true));
    eval!(comaprison_2, "(42 > 42) != (42 <= 42);" => Boolean(true));
    eval!(comaprison_3, "(42 == 42) == (42 >= 42);" => Boolean(true));
    eval!(comaprison_4, "(42 == 42) == (42 <= 42);" => Boolean(true));
    eval!(comaprison_5, "(42 > 42) == (42 < 42);" => Boolean(true));
    eval!(equality_bool_eq1, "true == true;" => Boolean(true));
    eval!(equality_bool_eq2, "false == false;" => Boolean(true));
    eval!(equality_bool_neq1, "true == false;" => Boolean(false));
    eval!(equality_bool_neq2, "false == true;" => Boolean(false));
    eval!(fibonacci_rec, r#"
        let f(n) = {
            if n <= 1 {
                ret n;
            }
            f(n - 1) + f(n - 2);
        }
        f(9) + 8;
    "# => Number(42));
    eval!(fibonacci_iter, r#"
        let f(n) = {
            if n == 0 { ret 0; }
            if n == 1 { ret 1; }

            let prev_prev = 0;
            let prev = 1;
            let current = 0;

            while n > 1 {
                current = prev_prev + prev;
                prev_prev = prev;
                prev = current;
                n = n - 1;
            }

            current;
        }
        f(9) + 8;
    "# => Number(42));
    eval!(wtf, r#"
        let wtf(i, j) = {
            ret if i > j {
                i + j;
            } else if i < 10 {
                i + 1;
            } else {
                j;
            };
        }

        let seven = wtf(5, 2);
        let tree = wtf(2, 3);
        let twenty_one = wtf(11, 21);

        seven * tree + twenty_one;
    "# => Number(42));
    eval!(fact, r#"
        let fact(n) = {
            let product = 1;
            while n > 0 {
                product = product * n;
                n = n - 1;
            }
            product;
        }
        fact(3);
    "# => Number(6));
}
