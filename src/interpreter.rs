use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::BinaryOperatorKind;
use crate::ast::{Ast, Visitor};

pub struct Interpreter;

impl Visitor<i64> for Interpreter {
    fn visit_ast(&mut self, ast: &Ast) -> i64 {
        ast.expression().accept(self)
    }

    fn visit_expression(&mut self, expr: &Expression) -> i64 {
        match expr.kind() {
            ExpressionKind::Literal(n) => n.accept(self),
            ExpressionKind::Binary(l, o, r) => {
                let l = l.accept(self);
                let r = r.accept(self);
                match o.kind() {
                    BinaryOperatorKind::Addition => l + r,
                    BinaryOperatorKind::Multiplication => l * r,
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
}
