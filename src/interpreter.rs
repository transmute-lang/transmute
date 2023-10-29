use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperatorKind, UnaryOperatorKind};
use crate::ast::statement::Statement;
use crate::ast::Visitor;

pub struct Interpreter;

impl Visitor<i64> for Interpreter {
    fn visit_statement(&mut self, stmt: &Statement) -> i64 {
        // todo this is wrong
        0
    }

    fn visit_expression(&mut self, expr: &Expression) -> i64 {
        match expr.kind() {
            ExpressionKind::Literal(n) => n.accept(self),
            ExpressionKind::Binary(l, o, r) => {
                let l = l.accept(self);
                let r = r.accept(self);
                match o.kind() {
                    BinaryOperatorKind::Addition => l + r,
                    BinaryOperatorKind::Subtraction => l - r,
                    BinaryOperatorKind::Multiplication => l * r,
                    BinaryOperatorKind::Division => l / r,
                }
            }
            ExpressionKind::Unary(o, e) => {
                let e = e.accept(self);
                match o.kind() {
                    UnaryOperatorKind::Minus => -e,
                }
            }
        }
    }

    fn visit_literal(&mut self, literal: &Literal) -> i64 {
        match literal.kind() {
            LiteralKind::Number(n) => *n,
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
            pub fn $name() {
                let mut parser = Parser::new(Lexer::new($src));
                let ast = parser.parse().expect("source is valid");

                let mut interpreter = Interpreter;
                let actual = ast.accept(&mut interpreter);

                assert_eq!($expected, actual)
            }
        };
    }

    eval!(simple_precedence_1, "2 + 20 * 2" => 42);
    eval!(simple_precedence_2, "20 * 2 + 2" => 42);
    eval!(parenthesis_precedence, "(20 + 1) * 2" => 42);
    eval!(negative_number, "-1 + 43" => 42);
    eval!(unary_operator_minus_number, "- 1 + 43" => 42);
    eval!(binary_operator_minus, "43 - 1" => 42);
    eval!(unary_operator_minus_negative_number, "--42" => 42);
    eval!(division, "85 / 2" => 42);

    eval!(let_stmt, "let forty_two = 42" => 0); // fixme should be a 'none' value
}
