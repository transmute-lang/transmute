use crate::ast::expression::{ExpressionKind, Target};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::StatementKind;
use crate::ast::ResolvedAst;
use crate::resolver::SymbolKind;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct Interpreter<'a> {
    ast: &'a ResolvedAst,
    /// Maps an identifier in the current frame to the value's index in the heap
    // todo IdentId should be SymbolId
    stack: Vec<HashMap<IdentId, Ref>>,
    heap: Vec<Value>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a ResolvedAst) -> Self {
        Self {
            ast,
            stack: vec![Default::default()],
            heap: Default::default(),
        }
    }

    pub fn start(&mut self) -> i64 {
        let val = self.visit_statements(self.ast.root_statements());
        let val = val
            .value_ref
            .map(|r| &self.heap[r.0])
            .cloned()
            .unwrap_or_default();

        match val {
            Value::Boolean(true) => 1,
            Value::Boolean(false) => 0,
            Value::Number(n) => n,
            Value::Struct(_) => {
                eprintln!("Cannot return a struct");
                0
            }
            Value::Void => 0,
        }
    }

    fn visit_statements(&mut self, statements: &[StmtId]) -> Val {
        let mut value = Val::none();

        for statement in statements {
            value = self.visit_statement(self.ast.statement(*statement).id());

            if value.is_ret {
                return value;
            }
        }

        value
    }

    fn visit_statement(&mut self, stmt: StmtId) -> Val {
        let stmt = self.ast.statement(stmt);
        match stmt.kind() {
            StatementKind::Expression(e) => self.visit_expression(*e),
            StatementKind::Let(ident, expr) => {
                let val = self.visit_expression(*expr);
                if val.is_ret {
                    return val;
                }

                self.stack
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.id(), val.value_ref.expect("rhs has value"));

                Val::none()
            }
            StatementKind::LetFn(_, _, _, _) => Val::none(),
            StatementKind::Ret(e, _) => Val::of_option_ret(self.visit_expression(*e).value_ref),
            StatementKind::Struct(_, _) => Val::none(),
        }
    }

    fn visit_expression(&mut self, expr: ExprId) -> Val {
        let expr = self.ast.expression(expr);
        match expr.kind() {
            ExpressionKind::Literal(n) => Val::of(self.visit_literal(n)),
            ExpressionKind::Binary(_, _, _) => unimplemented!(),
            ExpressionKind::Unary(_, _) => unimplemented!(),
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                let val = self.visit_expression(*expr_id);

                if val.is_ret {
                    return val;
                }

                let values = self.heap[val.value_ref.expect("expr exists").0].as_struct();

                match self.ast.symbol_by_ident_ref_id(*ident_ref_id).kind() {
                    SymbolKind::Field(_, index) => Val::of(values[*index]),
                    _ => panic!(),
                }
            }
            ExpressionKind::FunctionCall(ident, arguments) => {
                self.visit_function_call(ident, arguments)
            }
            ExpressionKind::Assignment(Target::Direct(ident), expr) => {
                self.visit_assignment(ident, expr)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                let (lhs_val, index) = match self.ast.expression(*lhs_expr_id).kind() {
                    ExpressionKind::Access(expr_id, ident_ref_id) => {
                        let val = self.visit_expression(*expr_id);
                        if val.is_ret {
                            return val;
                        }

                        let symbol = self.ast.symbol_by_ident_ref_id(*ident_ref_id);
                        match symbol.kind() {
                            SymbolKind::Field(_, index) => (val, index),
                            _ => panic!("field expected"),
                        }
                    }
                    _ => panic!("access expected"),
                };

                let rhs_val = self.visit_expression(*rhs_expr_id);
                if rhs_val.is_ret {
                    return rhs_val;
                }

                let lhs_val = self
                    .heap
                    .get_mut(lhs_val.value_ref.expect("lhs has value").0)
                    .expect("rhs value exists");
                let lhs_val = lhs_val.as_mut_struct();

                lhs_val[*index] = rhs_val.value_ref.expect("rhs has value");

                rhs_val
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(cond, true_branch, false_branch)
            }
            ExpressionKind::While(cond, expr) => self.visit_while(cond, expr),
            ExpressionKind::Block(_) => {
                todo!("implement block expression")
            }
            ExpressionKind::StructInstantiation(_, fields) => {
                let mut values = Vec::with_capacity(fields.len());
                for (_, expr_id) in fields {
                    let val = self.visit_expression(*expr_id);
                    if val.is_ret {
                        return val;
                    }
                    values.push(val.value_ref.expect("field has value"));
                }
                self.heap.push(Value::Struct(values));

                Val::of(Ref(self.heap.len() - 1))
            }
            ExpressionKind::Dummy => {
                panic!("should not interpret an invalid source code")
            }
        }
    }

    fn visit_literal(&mut self, literal: &Literal) -> Ref {
        match literal.kind() {
            LiteralKind::Number(n) => {
                self.heap.push(Value::Number(*n));
                Ref(self.heap.len() - 1)
            }
            LiteralKind::Identifier(ident_ref_id) => {
                let ident = self.ast.identifier_ref(*ident_ref_id).ident();
                match self
                    .stack
                    .last_mut()
                    .expect("there is an env")
                    .get(&ident.id())
                {
                    None => {
                        panic!("{} not in scope", self.ast.identifier(ident.id()))
                    }
                    Some(v) => *v,
                }
            }
            LiteralKind::Boolean(b) => {
                self.heap.push(Value::Boolean(*b));
                Ref(self.heap.len() - 1)
            }
        }
    }

    fn visit_function_call(&mut self, ident: &IdentRefId, arguments: &[ExprId]) -> Val {
        match self.ast.symbol_by_ident_ref_id(*ident).kind() {
            SymbolKind::Let(_)
            | SymbolKind::Parameter(_, _)
            | SymbolKind::Field(_, _)
            | SymbolKind::Struct(_)
            | SymbolKind::NativeType(_, _) => {
                panic!("let fn expected")
            }
            SymbolKind::LetFn(stmt, _, _) => {
                let stmt = self.ast.statement(*stmt);
                match stmt.kind() {
                    StatementKind::LetFn(_, parameters, _, expr) => {
                        let expr = self.ast.expression(*expr);
                        match expr.kind() {
                            ExpressionKind::Block(stmts) => {
                                let mut env = HashMap::with_capacity(parameters.len());

                                for (param, expr_id) in parameters.iter().zip(arguments.iter()) {
                                    let val = self.visit_expression(*expr_id);
                                    if val.is_ret {
                                        return val;
                                    }
                                    env.insert(
                                        param.identifier().id(),
                                        val.value_ref.expect("param has value"),
                                    );
                                }

                                self.stack.push(env);

                                let ret = self.visit_statements(stmts);

                                let _ = self.stack.pop();

                                Val::of_option(ret.value_ref)
                            }
                            _ => panic!("block expected"),
                        }
                    }
                    _ => panic!("let fn expected"),
                }
            }
            SymbolKind::Native(_, _, _, body) => {
                let mut env = Vec::with_capacity(arguments.len());

                for expr_id in arguments {
                    // fixme not always: a Void could be returned
                    let val = self.visit_expression(*expr_id);
                    if val.is_ret {
                        return val;
                    }
                    env.push(val);
                }

                let env = env
                    .into_iter()
                    // fixme should be a ref?
                    .map(|val| self.heap[val.value_ref.expect("param has value").0].clone())
                    .collect::<Vec<Value>>();

                self.heap.push(body.call(env));

                Val::of(Ref(self.heap.len() - 1))
            }
            SymbolKind::NotFound => panic!(),
        }
    }

    fn visit_assignment(&mut self, ident_ref_id: &IdentRefId, expr: &ExprId) -> Val {
        let ident = self.ast.identifier_ref(*ident_ref_id).ident();
        if !self
            .stack
            .last()
            .expect("there is an env")
            .contains_key(&ident.id())
        {
            panic!("{} not in scope", self.ast.identifier(ident.id()));
        }

        let val = self.visit_expression(*expr);
        if !val.is_ret {
            self.stack
                .last_mut()
                .expect("there is an env")
                .insert(ident.id(), val.value_ref.expect("rhs has value"));
        }

        val
    }

    fn visit_if(
        &mut self,
        cond: &ExprId,
        true_branch: &ExprId,
        false_branch: &Option<ExprId>,
    ) -> Val {
        let val = self.visit_expression(*cond);
        if val.is_ret {
            return val;
        }
        let cond = self.heap[val.value_ref.expect("condition has value").0].as_bool();

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
            Val::none()
        }
    }

    fn visit_while(&mut self, cond: &ExprId, expr: &ExprId) -> Val {
        let statements = match self.ast.expression(*expr).kind() {
            ExpressionKind::Block(statements) => statements,
            _ => panic!("block expected"),
        };

        let mut ret = Val::none();
        loop {
            let val = self.visit_expression(*cond);
            if val.is_ret {
                return val;
            }
            if !self.heap[val.value_ref.expect("condition has value").0].as_bool() {
                return ret;
            }

            ret = self.visit_statements(statements);
        }
    }
}

impl<'a> Interpreter<'a> {}

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Value {
    Boolean(bool),
    Number(i64),
    Struct(Vec<Ref>),
    #[default]
    Void,
}

impl Value {
    pub fn as_i64(&self) -> i64 {
        match self {
            Value::Number(n) => *n,
            _ => panic!("{} is not a number", self),
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Value::Boolean(b) => *b,
            _ => panic!("{} is not a bool", self),
        }
    }

    pub fn as_struct(&self) -> &Vec<Ref> {
        match self {
            Value::Struct(v) => v,
            _ => panic!("{} is not a struct", self),
        }
    }

    fn as_mut_struct(&mut self) -> &mut Vec<Ref> {
        match self {
            Value::Struct(v) => v,
            _ => panic!("{} is not a struct", self),
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
            Value::Struct(values) => {
                write!(f, "{{")?;
                for (index, value) in values.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", value)?;
                }
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub struct Ref(usize);

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.0)
    }
}

struct Val {
    value_ref: Option<Ref>,
    is_ret: bool,
}

impl Val {
    fn none() -> Self {
        Self {
            value_ref: None,
            is_ret: false,
        }
    }

    fn of(r: Ref) -> Self {
        Self {
            value_ref: Some(r),
            is_ret: false,
        }
    }

    fn of_option(r: Option<Ref>) -> Self {
        Self {
            value_ref: r,
            is_ret: false,
        }
    }

    fn of_option_ret(r: Option<Ref>) -> Self {
        Self {
            value_ref: r,
            is_ret: true,
        }
    }
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
        ($name:ident, $src:expr => $value:expr) => {
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

                assert_eq!(actual, $value)
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

    eval!(simple_precedence_1, "2 + 20 * 2;" => 42);
    eval!(simple_precedence_2, "20 * 2 + 2;" => 42);
    eval!(parenthesis_precedence, "(20 + 1) * 2;" => 42);
    eval!(negative_number, "-1 + 43;" => 42);
    eval!(unary_operator_minus_number, "- 1 + 43;" => 42);
    eval!(binary_operator_minus, "43 - 1;" => 42);
    eval!(unary_operator_minus_negative_number, "--42;" => 42);
    eval!(division, "85 / 2;" => 42);
    eval!(let_stmt, "let forty_two = 42;" => 0);
    eval!(let_stmt_then_expression, "let forty = 2 * 20; forty + 2;" => 42);
    eval!(function, "let times_two(v: number): number = v * 2;" => 0);
    eval!(function_call, "let times_two(v: number): number = v * 2; times_two(21);" => 42);
    eval!(complex_function_call, "let plus_one_times_two(v: number): number = { let res = v + 1; res * 2; } plus_one_times_two(20);" => 42);
    eval!(ret_function_call, "let times_two(v: number): number = { 41; ret v * 2; 42; } times_two(21);" => 42);
    eval!(bool_true, "true;" => 1);
    eval!(bool_false, "false;" => 0);
    eval!(equality_numbers_eq_true, "42 == 42;" => 1);
    eval!(equality_numbers_eq_false, "42 == 41;" => 0);
    eval!(equality_numbers_neq_true, "42 != 42;" => 0);
    eval!(equality_numbers_neq_false, "42 != 42;" => 0);
    eval!(equality_booleans_eq_true, "true == true;" => 1);
    eval!(equality_booleans_eq_false, "true == false;" => 0);
    eval!(equality_booleans_neq_true, "true != true;" => 0);
    eval!(equality_booleans_neq_false, "true != false;" => 1);
    eval!(comaprison_1, "(42 > 42) != (42 >= 42);" => 1);
    eval!(comaprison_2, "(42 > 42) != (42 <= 42);" => 1);
    eval!(comaprison_3, "(42 == 42) == (42 >= 42);" => 1);
    eval!(comaprison_4, "(42 == 42) == (42 <= 42);" => 1);
    eval!(comaprison_5, "(42 > 42) == (42 < 42);" => 1);
    eval!(equality_bool_eq1, "true == true;" => 1);
    eval!(equality_bool_eq2, "false == false;" => 1);
    eval!(equality_bool_neq1, "true == false;" => 0);
    eval!(equality_bool_neq2, "false == true;" => 0);
    eval!(fibonacci_rec, r#"
        let f(n: number): number = {
            if n <= 1 {
                ret n;
            }
            f(n - 1) + f(n - 2);
        }
        f(9) + 8;
    "# => 42);
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
    "# => 42);
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
    "# => 42);
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
    "# => 6);
    eval!(area, r#"
        struct Point {
            x: number,
            y: number
        }
        let area(p1: Point, p2: Point): number = {
            (p2.x - p1.x) * (p2.y - p1.y);
        }
        area(
            Point {
                x: 1,
                y: 1
            },
            Point {
                x: 1 + 6,
                y: 1 + 7
            }
        );
    "# => 42);
    eval!(area_nested_struct, r#"
        struct Point {
            x: number,
            y: number
        }

        struct Square {
            p1: Point,
            p2: Point
        }

        let area(s: Square): number = {
            (s.p2.x - s.p1.x) * (s.p2.y - s.p1.y);
        }

        let p1 = Point {
            x: 1,
            y: 1
        };

        let p2 = Point {
            x: 6,
            y: 7
        };

        p2.x = p2.x + 1;
        p2.y = p2.y + 1;

        area(
            Square {
                p1: p1,
                p2: p2
            }
        );
    "# => 42);
}
