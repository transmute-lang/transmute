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

    #[test]
    pub fn interpret() {
        let lexer = Lexer::new("2 + 20 * 2");
        let mut parser = Parser::new(lexer);

        let ast = parser.parse().unwrap();

        let mut interpreter = Interpreter;
        let x = ast.accept(&mut interpreter);

        assert_eq!(42, x);
    }
}
