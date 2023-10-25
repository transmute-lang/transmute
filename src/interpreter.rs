use crate::ast::{Ast, Visitor};
use crate::parser::{Literal, LiteralKind};

pub struct Interpreter;

impl Visitor<i64> for Interpreter {
    fn visit(&mut self, ast: &Ast) -> i64 {
        match ast.root {
            Literal {
                kind: LiteralKind::Number(n),
                ..
            } => n,
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
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let ast = parser.parse().unwrap();

        let mut interpreter = Interpreter;
        let x = ast.accept(&mut interpreter);

        assert_eq!(42, x);
    }
}
