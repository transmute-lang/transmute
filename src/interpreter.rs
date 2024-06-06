use crate::ast::expression::ExpressionKind;
use crate::ast::identifier_ref::Bound;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Statement, StatementKind};
use crate::ast::ResolvedAst;
use crate::resolver::{SymbolKind, Type};
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct Interpreter<'a> {
    ast: &'a ResolvedAst,
    // todo IdentId should be SymbolId
    // todo turn into frame
    variables: Vec<HashMap<IdentId, Value>>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a ResolvedAst) -> Self {
        Self {
            ast,
            variables: vec![Default::default()],
        }
    }

    pub fn start(&mut self) -> Value {
        self.visit_statements(self.ast.root_statements())
    }

    fn visit_statements(&mut self, statements: &[StmtId]) -> Value {
        let mut value = Value::Void;

        for statement in statements {
            let statement = self.ast.statement(*statement);
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

    fn visit_statement(&mut self, stmt: StmtId) -> Value {
        let stmt = self.ast.statement(stmt);
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
            StatementKind::LetFn(_, _, _, _) => {
                Value::Void // todo this is wrong
            }
            StatementKind::Ret(e, _) => self.visit_expression(*e),
        }
    }

    fn visit_expression(&mut self, expr: ExprId) -> Value {
        let expr = self.ast.expression(expr);
        match expr.kind() {
            ExpressionKind::Literal(n) => self.visit_literal(n),
            ExpressionKind::Binary(_, _, _) => unimplemented!(),
            ExpressionKind::Unary(_, _) => unimplemented!(),
            ExpressionKind::FunctionCall(ident, arguments) => {
                self.visit_function_call(ident, arguments)
            }
            ExpressionKind::Assignment(ident, expr) => self.visit_assignment(ident, expr),
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(cond, true_branch, false_branch)
            }
            ExpressionKind::While(cond, expr) => self.visit_while(cond, expr),
            ExpressionKind::Block(_) => {
                todo!("implement block expression")
            }
            ExpressionKind::Dummy => {
                panic!("should not interpret an invalid source code")
            }
        }
    }

    fn visit_literal(&mut self, literal: &Literal) -> Value {
        match literal.kind() {
            LiteralKind::Number(n) => Value::Number(*n),
            LiteralKind::Identifier(ident) => {
                let ident = self.ast.identifier_ref(*ident).ident();
                match self
                    .variables
                    .last_mut()
                    .expect("there is an env")
                    .get(&ident.id())
                {
                    None => {
                        panic!("{} not in scope", self.ast.identifier(ident.id()))
                    }
                    Some(v) => v.clone(),
                }
            }
            LiteralKind::Boolean(b) => Value::Boolean(*b),
        }
    }

    fn visit_function_call(&mut self, ident: &IdentRefId, arguments: &[ExprId]) -> Value {
        let ident_ref = self.ast.identifier_ref(*ident);
        let symbol = self.ast.symbol(ident_ref.symbol_id());
        match symbol.kind() {
            SymbolKind::NotFound => panic!(),
            SymbolKind::Let(_) | SymbolKind::Parameter(_, _) | SymbolKind::NativeType(_) => {
                panic!("let fn expected")
            }
            SymbolKind::LetFn(stmt, _, _) => {
                let stmt = self.ast.statement(*stmt);
                match stmt.kind() {
                    StatementKind::LetFn(_, parameters, _, expr) => {
                        let expr = self.ast.expression(*expr);
                        match expr.kind() {
                            ExpressionKind::Block(stmts) => {
                                let env = parameters
                                    .iter()
                                    .zip(arguments.iter())
                                    .map(|(param, expr)| {
                                        (param.identifier().id(), self.visit_expression(*expr))
                                    })
                                    .collect::<HashMap<IdentId, Value>>();

                                self.variables.push(env);

                                let ret = self.visit_statements(stmts).unwrap();

                                let _ = self.variables.pop();

                                ret
                            }
                            _ => panic!("block expected"),
                        }
                    }
                    _ => panic!("let fn expected"),
                }
            }
            SymbolKind::Native(_, _, _, body) => {
                let env = arguments
                    .iter()
                    .map(|expr| self.visit_expression(*expr))
                    .collect::<Vec<Value>>();

                body(env)
            }
        }
    }

    fn visit_assignment(&mut self, ident: &IdentRefId, expr: &ExprId) -> Value {
        let ident = self.ast.identifier_ref(*ident).ident();
        if !self
            .variables
            .last()
            .expect("there is an env")
            .contains_key(&ident.id())
        {
            panic!("{} not in scope", self.ast.identifier(ident.id()));
        }

        let val = self.visit_expression(*expr);

        self.variables
            .last_mut()
            .expect("there is an env")
            .insert(ident.id(), val.clone());

        val
    }

    fn visit_if(
        &mut self,
        cond: &ExprId,
        true_branch: &ExprId,
        false_branch: &Option<ExprId>,
    ) -> Value {
        let cond = self.visit_expression(*cond);
        let cond = match cond {
            Value::Boolean(b) => b,
            _ => panic!("condition is not a boolean"),
        };

        let statements = if cond {
            Some(true_branch)
        } else {
            false_branch.as_ref()
        }
        .map(|expr| match self.ast.expression(*expr).kind() {
            ExpressionKind::Block(statements) => statements,
            _ => panic!("block expected"),
        });

        if let Some(statements) = statements {
            self.visit_statements(statements)
        } else {
            Value::Void
        }
    }

    fn visit_while(&mut self, cond: &ExprId, expr: &ExprId) -> Value {
        let statements = match self.ast.expression(*expr).kind() {
            ExpressionKind::Block(statements) => statements,
            _ => panic!("block expected"),
        };

        let mut ret = Value::Void;
        loop {
            match self.visit_expression(*cond) {
                Value::Boolean(false) => return ret,
                Value::Boolean(true) => {}
                _ => panic!("condition is not a boolean"),
            };

            ret = self.visit_statements(statements);
        }
    }
}

impl<'a> Interpreter<'a> {}

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

    pub fn ty(&self) -> Type {
        match self {
            Value::Boolean(_) => Type::Boolean,
            Value::Number(_) => Type::Number,
            Value::RetVal(v) => v.ty(),
            Value::Void => Type::Void,
        }
    }

    pub fn try_to_i64(self) -> i64 {
        match self {
            Value::Number(n) => n,
            _ => panic!("{} is not a number", self),
        }
    }

    pub fn try_to_bool(self) -> bool {
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

fn is_ret(s: &Statement<Bound>) -> bool {
    matches!(s.kind(), &StatementKind::Ret(_, _))
}

#[cfg(test)]
mod tests {
    use crate::desugar::ImplicitRetConverter;
    use crate::interpreter::Interpreter;
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;

    macro_rules! eval {
        ($name:ident, $src:expr => $kind:ident($value:expr)) => {
            #[test]
            fn $name() {
                let parser = Parser::new(Lexer::new($src));
                let ast = parser
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRetConverter::new())
                    .resolve(Resolver::new(), Natives::default())
                    .unwrap();

                let actual = Interpreter::new(&ast).start();

                assert_eq!(actual, super::Value::$kind($value))
            }
        };
        ($name:ident, $src:expr => $kind:ident) => {
            #[test]
            fn $name() {
                let parser = Parser::new(Lexer::new($src));
                let ast = parser
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRetConverter::new())
                    .resolve(Resolver::new(), Natives::new())
                    .unwrap();

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
    eval!(function, "let times_two(v: number): number = v * 2;" => Void);
    eval!(function_call, "let times_two(v: number): number = v * 2; times_two(21);" => Number(42));
    eval!(complex_function_call, "let plus_one_times_two(v: number): number = { let res = v + 1; res * 2; } plus_one_times_two(20);" => Number(42));
    eval!(ret_function_call, "let times_two(v: number): number = { 41; ret v * 2; 42; } times_two(21);" => Number(42));
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
        let f(n: number): number = {
            if n <= 1 {
                ret n;
            }
            f(n - 1) + f(n - 2);
        }
        f(9) + 8;
    "# => Number(42));
    eval!(fibonacci_iter, r#"
        let f(n: number): number = {
            if n == 0 { ret 0; }
            if n == 1 { ret 1; }

            let n = n;
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
        let wtf(i: number, j: number): number = {
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
        let fact(n: number): number = {
            let n = n;
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
