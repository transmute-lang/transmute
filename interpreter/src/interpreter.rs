use crate::value::{Ref, Value};
use std::collections::HashMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId};
use transmute_hir::expression::{ExpressionKind, Target};
use transmute_hir::literal::{Literal, LiteralKind};
use transmute_hir::natives::NativeFnKind;
use transmute_hir::statement::{Implementation, StatementKind};
use transmute_hir::symbol::SymbolKind;
use transmute_hir::ResolvedHir;

pub struct Interpreter<'a> {
    hir: &'a ResolvedHir,
    /// Maps an identifier in the current frame to the value's index in the heap
    // todo:refactoring IdentId should be SymbolId
    stack: Vec<HashMap<IdentId, Ref>>,
    heap: Vec<Value>,
}

impl<'a> Interpreter<'a> {
    pub fn new(ast: &'a ResolvedHir) -> Self {
        Self {
            hir: ast,
            stack: vec![Default::default()],
            heap: Default::default(),
        }
    }

    pub fn start(&mut self, main_parameters: Vec<Value>) -> i64 {
        let (parameters, implementation) = self
            .hir
            .roots
            .iter()
            .filter_map(|stmt_id| {
                if let StatementKind::LetFn(ident, _, params, _, implementation) =
                    &self.hir.statements[*stmt_id].kind
                {
                    if &self.hir.identifiers[ident.id] == "main" {
                        return Some((params, *implementation));
                    }
                }
                None
            })
            .next()
            .expect("main function exists");

        let expr_id = match implementation {
            Implementation::Provided(expr_id) => expr_id,
            #[cfg(debug_assertions)]
            Implementation::Native(_) => {
                panic!("native functions are not supported in interpreter")
            }
            #[cfg(not(debug_assertions))]
            Implementation::Native => {
                panic!("native functions are not supported in interpreter")
            }
        };
        let val = match &self.hir.expressions[expr_id].kind {
            ExpressionKind::Block(stmts) => {
                let mut env = HashMap::with_capacity(parameters.len());

                for (param, value) in parameters.iter().zip(main_parameters.into_iter()) {
                    self.heap.push(value);
                    env.insert(param.identifier.id, Ref(self.heap.len() - 1));
                }

                self.stack.push(env);

                let ret = self.visit_statements(stmts);

                let _ = self.stack.pop();

                Val::of_option(ret.value_ref)
            }
            _ => panic!("block expected as main function body"),
        };

        let val = val
            .value_ref
            .map(|r| &self.heap[r.0])
            .cloned()
            .unwrap_or_default();

        match val {
            Value::Boolean(true) => 1,
            Value::Boolean(false) => 0,
            Value::Number(n) => n,
            Value::String(_) => {
                eprintln!("Cannot return a string");
                0
            }
            Value::Struct(_) => {
                eprintln!("Cannot return a struct");
                0
            }
            Value::Array(_) => {
                eprintln!("Cannot return an array");
                0
            }
            Value::Void => 0,
        }
    }

    fn visit_statements(&mut self, statements: &[StmtId]) -> Val {
        let mut value = Val::none();

        for statement in statements {
            value = self.visit_statement(self.hir.statements[*statement].id);

            if value.is_ret {
                return value;
            }
        }

        value
    }

    fn visit_statement(&mut self, stmt: StmtId) -> Val {
        let stmt = &self.hir.statements[stmt];
        match &stmt.kind {
            StatementKind::Expression(e) => self.visit_expression(*e),
            StatementKind::Let(ident, expr) => {
                let val = self.visit_expression(*expr);
                if val.is_ret {
                    return val;
                }

                self.stack
                    .last_mut()
                    .expect("there is an env")
                    .insert(ident.id, val.value_ref.expect("rhs has value"));

                Val::none()
            }
            StatementKind::LetFn(_, _, _, _, _) => Val::none(),
            StatementKind::Ret(None, _) => Val::of_option_ret(None),
            StatementKind::Ret(Some(e), _) => {
                Val::of_option_ret(self.visit_expression(*e).value_ref)
            }
            StatementKind::Struct(_, _, _) => Val::none(),
            StatementKind::Annotation(_) => Val::none(),
        }
    }

    fn visit_expression(&mut self, expr: ExprId) -> Val {
        let expr = &self.hir.expressions[expr];
        match &expr.kind {
            ExpressionKind::Literal(n) => Val::of(self.visit_literal(n)),
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                let val = self.visit_expression(*expr_id);

                if val.is_ret {
                    return val;
                }

                let values = self.heap[val.value_ref.expect("expr exists").0].as_struct();

                match &self.hir.symbol_by_ident_ref_id(*ident_ref_id).kind {
                    SymbolKind::Field(_, _, index) => Val::of(values[*index]),
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
                let rhs_val = self.visit_expression(*rhs_expr_id);
                if rhs_val.is_ret {
                    return rhs_val;
                }

                let (lhs_val, index) = match &self.hir.expressions[*lhs_expr_id].kind {
                    ExpressionKind::Access(expr_id, ident_ref_id) => {
                        let val = self.visit_expression(*expr_id);
                        if val.is_ret {
                            return val;
                        }

                        let symbol = self.hir.symbol_by_ident_ref_id(*ident_ref_id);
                        let index = match &symbol.kind {
                            SymbolKind::Field(_, _, index) => *index,
                            _ => panic!("field expected"),
                        };

                        let val = self
                            .heap
                            .get_mut(val.value_ref.expect("lhs has value").0)
                            .expect("rhs value exists");

                        (val.as_mut_struct(), index)
                    }
                    ExpressionKind::ArrayAccess(base, index) => {
                        let base = self.visit_expression(*base);
                        if base.is_ret {
                            return base;
                        }

                        let index = self.visit_expression(*index);
                        if index.is_ret {
                            return index;
                        }

                        let index = self.heap[index.value_ref.expect("index exists").0].as_i64();

                        let base = self
                            .heap
                            .get_mut(base.value_ref.expect("lhs has value").0)
                            .expect("rhs value exists");

                        (base.as_mut_array(), index as usize)
                    }
                    _ => panic!("either struct access or array access expected"),
                };

                lhs_val[index] = rhs_val.value_ref.expect("rhs has value");

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
            ExpressionKind::ArrayInstantiation(elements) => {
                let mut values = Vec::with_capacity(elements.len());
                for expr_id in elements {
                    let val = self.visit_expression(*expr_id);
                    if val.is_ret {
                        return val;
                    }
                    values.push(val.value_ref.expect("field has value"));
                }
                self.heap.push(Value::Array(values));

                Val::of(Ref(self.heap.len() - 1))
            }
            ExpressionKind::ArrayAccess(base, index) => {
                let base = self.visit_expression(*base);
                if base.is_ret {
                    return base;
                }

                let index = self.visit_expression(*index);
                if index.is_ret {
                    return index;
                }

                let values = self.heap[base.value_ref.expect("base exists").0].as_array();
                let index = self.heap[index.value_ref.expect("index exists").0].as_i64();

                Val::of(values[index as usize])
            }
        }
    }

    fn visit_literal(&mut self, literal: &Literal) -> Ref {
        match &literal.kind {
            LiteralKind::Number(n) => {
                self.heap.push(Value::Number(*n));
                Ref(self.heap.len() - 1)
            }
            LiteralKind::Identifier(ident_ref_id) => {
                let ident = &self.hir.identifier_refs[*ident_ref_id].ident;
                match self
                    .stack
                    .last_mut()
                    .expect("there is an env")
                    .get(&ident.id)
                {
                    None => {
                        panic!("{} not in scope", self.hir.identifiers[ident.id])
                    }
                    Some(v) => *v,
                }
            }
            LiteralKind::Boolean(b) => {
                self.heap.push(Value::Boolean(*b));
                Ref(self.heap.len() - 1)
            }
            LiteralKind::String(s) => {
                self.heap.push(Value::String(s.clone()));
                Ref(self.heap.len() - 1)
            }
        }
    }

    fn visit_function_call(&mut self, ident: &IdentRefId, arguments: &[ExprId]) -> Val {
        match &self.hir.symbol_by_ident_ref_id(*ident).kind {
            SymbolKind::Let(_, _)
            | SymbolKind::Parameter(_, _, _)
            | SymbolKind::Field(_, _, _)
            | SymbolKind::Struct(_, _)
            | SymbolKind::Annotation(_, _)
            | SymbolKind::NativeType(_, _) => {
                panic!("let fn expected")
            }
            SymbolKind::LetFn(_, stmt, _, _) => {
                let stmt = &self.hir.statements[*stmt];
                match &stmt.kind {
                    StatementKind::LetFn(_, _, parameters, _, implementation) => {
                        let expr_id = match implementation {
                            Implementation::Provided(expr_id) => expr_id,
                            #[cfg(debug_assertions)]
                            Implementation::Native(_) => {
                                panic!("native functions are not supported in interpreter")
                            }
                            #[cfg(not(debug_assertions))]
                            Implementation::Native => {
                                panic!("native functions are not supported in interpreter")
                            }
                        };
                        let expr = &self.hir.expressions[*expr_id];
                        match &expr.kind {
                            ExpressionKind::Block(stmts) => {
                                let mut env = HashMap::with_capacity(parameters.len());

                                for (param, expr_id) in parameters.iter().zip(arguments.iter()) {
                                    let val = self.visit_expression(*expr_id);
                                    if val.is_ret {
                                        return val;
                                    }
                                    env.insert(
                                        param.identifier.id,
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
            SymbolKind::Native(_, _, _, kind) => {
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
                    // todo:refactoring should be a ref?
                    .map(|val| self.heap[val.value_ref.expect("param has value").0].clone())
                    .collect::<Vec<Value>>();

                self.heap.push(kind.call(env));

                Val::of(Ref(self.heap.len() - 1))
            }
            SymbolKind::NotFound => panic!("symbol was not resolved"),
        }
    }

    fn visit_assignment(&mut self, ident_ref_id: &IdentRefId, expr: &ExprId) -> Val {
        let ident = &self.hir.identifier_refs[*ident_ref_id].ident;
        if !self
            .stack
            .last()
            .expect("there is an env")
            .contains_key(&ident.id)
        {
            panic!("{} not in scope", self.hir.identifiers[ident.id]);
        }

        let val = self.visit_expression(*expr);
        if !val.is_ret {
            self.stack
                .last_mut()
                .expect("there is an env")
                .insert(ident.id, val.value_ref.expect("rhs has value"));
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
        .map(|expr| match &self.hir.expressions[*expr].kind {
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
        let statements = match &self.hir.expressions[*expr].kind {
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

trait RuntimeImpl {
    fn call(&self, parameters: Vec<Value>) -> Value;
}

impl RuntimeImpl for NativeFnKind {
    fn call(&self, mut parameters: Vec<Value>) -> Value {
        match self {
            NativeFnKind::NegNumber => Value::Number(-parameters.pop().unwrap().as_i64()),
            NativeFnKind::AddNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Number(left + right)
            }
            NativeFnKind::SubNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Number(left - right)
            }
            NativeFnKind::MulNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Number(left * right)
            }
            NativeFnKind::DivNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Number(left / right)
            }
            NativeFnKind::EqNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left == right)
            }
            NativeFnKind::NeqNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left != right)
            }
            NativeFnKind::GtNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left > right)
            }
            NativeFnKind::LtNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left < right)
            }
            NativeFnKind::GeNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left >= right)
            }
            NativeFnKind::LeNumberNumber => {
                let right = parameters.pop().unwrap().as_i64();
                let left = parameters.pop().unwrap().as_i64();
                Value::Boolean(left <= right)
            }
            NativeFnKind::EqBooleanBoolean => {
                let right = parameters.pop().unwrap().as_bool();
                let left = parameters.pop().unwrap().as_bool();
                Value::Boolean(left == right)
            }
            NativeFnKind::NeqBooleanBoolean => {
                let right = parameters.pop().unwrap().as_bool();
                let left = parameters.pop().unwrap().as_bool();
                Value::Boolean(left != right)
            }
            NativeFnKind::PrintNumber => {
                let number = parameters.pop().unwrap().as_i64();
                println!("{number}");
                Value::Void
            }
            NativeFnKind::PrintBoolean => {
                let bool = parameters.pop().unwrap().as_bool();
                println!("{bool}");
                Value::Void
            }
            NativeFnKind::PrintString => {
                let val = parameters.pop().unwrap();
                println!("{}", val.as_str());
                Value::Void
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::interpreter::Interpreter;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_hir::natives::Natives;
    use transmute_hir::UnresolvedHir;

    macro_rules! eval {
        ($name:ident, $src:expr => $value:expr) => {
            #[test]
            fn $name() {
                let hir = UnresolvedHir::from(Parser::new(Lexer::new($src)).parse().unwrap())
                    .resolve(Natives::default())
                    .unwrap();

                let actual = Interpreter::new(&hir).start(vec![]);

                assert_eq!(actual, $value)
            }
        }; // ($name:ident, $src:expr => $kind:ident) => {
           //     #[test]
           //     fn $name() {
           //         let parser = Parser::new(Lexer::new($src));
           //         let ast = parser
           //             .parse()
           //             .unwrap()
           //             .convert_implicit_ret()
           //             .convert_operators()
           //             .resolve(Natives::new())
           //             .unwrap();
           //
           //         let actual = Interpreter::new(&ast).start();
           //
           //         assert_eq!(actual, super::Value::$kind)
           //     }
           // };
    }

    eval!(simple_precedence_1, "let main() { 2 + 20 * 2; }" => 42);
    eval!(simple_precedence_2, "let main() { 20 * 2 + 2; }" => 42);
    eval!(parenthesis_precedence, "let main() { (20 + 1) * 2; }" => 42);
    eval!(negative_number, "let main() { -1 + 43; }" => 42);
    eval!(unary_operator_minus_number, "let main() { - 1 + 43; }" => 42);
    eval!(binary_operator_minus, "let main() { 43 - 1; }" => 42);
    eval!(unary_operator_minus_negative_number, "let main() { --42; }" => 42);
    eval!(division, "let main() { 85 / 2; }" => 42);
    eval!(let_stmt, "let main() {  let forty_two = 42; }" => 0);
    eval!(let_stmt_then_expression, "let main() {  let forty = 2 * 20; forty + 2; }" => 42);
    eval!(function, "let main() {  let times_two(v: number): number = v * 2; }" => 0);
    eval!(function_call, "let main() {  let times_two(v: number): number = v * 2; times_two(21); }" => 42);
    eval!(complex_function_call, "let main() {  let plus_one_times_two(v: number): number = { let res = v + 1; res * 2; } plus_one_times_two(20); }" => 42);
    eval!(ret_function_call, "let main() {  let times_two(v: number): number = { 41; ret v * 2; 43; } times_two(21); }" => 42);
    eval!(bool_true, "let main() {  true; }" => 1);
    eval!(bool_false, "let main() {  false; }" => 0);
    eval!(equality_numbers_eq_true, "let main() {  42 == 42; }" => 1);
    eval!(equality_numbers_eq_false, "let main() {  42 == 41; }" => 0);
    eval!(equality_numbers_neq_true, "let main() {  42 != 42; }" => 0);
    eval!(equality_numbers_neq_false, "let main() {  42 != 42; }" => 0);
    eval!(equality_booleans_eq_true, "let main() {  true == true; }" => 1);
    eval!(equality_booleans_eq_false, "let main() {  true == false; }" => 0);
    eval!(equality_booleans_neq_true, "let main() {  true != true; }" => 0);
    eval!(equality_booleans_neq_false, "let main() {  true != false; }" => 1);
    eval!(gt, "let main() {  42 > 42; }" => 0);
    eval!(lt, "let main() {  42 < 42; }" => 0);
    eval!(ge, "let main() {  42 >= 42; }" => 1);
    eval!(le, "let main() {  42 <= 42; }" => 1);
    eval!(comparison_1, "let main() {  (42 > 42) != (42 >= 42); }" => 1);
    eval!(comparison_2, "let main() {  (42 > 42) != (42 <= 42); }" => 1);
    eval!(comparison_3, "let main() {  (42 == 42) == (42 >= 42); }" => 1);
    eval!(comparison_4, "let main() {  (42 == 42) == (42 <= 42); }" => 1);
    eval!(comparison_5, "let main() {  (42 > 42) == (42 < 42); }" => 1);
    eval!(equality_bool_eq1, "let main() {  true == true; }" => 1);
    eval!(equality_bool_eq2, "let main() {  false == false; }" => 1);
    eval!(equality_bool_neq1, "let main() {  true == false; }" => 0);
    eval!(equality_bool_neq2, "let main() {  false == true; }" => 0);
    eval!(fibonacci_rec, r#"
        let f(n: number): number = {
            if n <= 1 {
                ret n;
            }
            f(n - 1) + f(n - 2);
        }

        let main() {
            f(9) + 8;
        }
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

        let main() {
            f(9) + 8;
        }
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

        let main() {
            let seven = wtf(5, 2);
            let tree = wtf(2, 3);
            let twenty_one = wtf(11, 21);

            seven * tree + twenty_one;
        }
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

        let main() {
            fact(3);
        }
    "# => 6);
    eval!(area, r#"
        struct Point {
            x: number,
            y: number
        }

        let area(p1: Point, p2: Point): number = {
            (p2.x - p1.x) * (p2.y - p1.y);
        }

        let main() {
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
        }
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

        let main() {
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
        }
    "# => 42);
}
