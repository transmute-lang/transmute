use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind};
use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, Location, Span, TokenKind};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Ast, Error> {
        let root = self.parse_expression()?;
        Ok(Ast::new(root))
    }

    fn parse_expression(&mut self) -> Result<Expression, Error> {
        let left = self.parse_literal()?;
        let op = self.parse_binary_operator()?;
        let right = self.parse_literal()?;

        Ok(Expression::from(ExpressionKind::Binary(
            Box::new(Expression::from(left)),
            op,
            Box::new(Expression::from(right)),
        )))
    }

    fn parse_literal(&mut self) -> Result<Literal, Error> {
        let token = self.lexer.next()?;

        match token.kind() {
            TokenKind::Number(n) => Ok(Literal::new(
                LiteralKind::Number(*n),
                token.location().clone(),
                token.span().clone(),
            )),
            _ => todo!("error handling"),
        }
    }

    fn parse_binary_operator(&mut self) -> Result<BinaryOperator, Error> {
        let token = self.lexer.next()?;

        match token.kind() {
            TokenKind::Plus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Addition,
                token.location().clone(),
                token.span().clone(),
            )),
            _ => todo!("error handling"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn literal() {
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let location = Location::new(1, 1);
        let span = Span::new(0, 2);

        let actual = parser.parse_literal().unwrap();
        let expected = Literal::new(
            LiteralKind::Number(42),
            location,
            span,
        );

        assert_eq!(expected, actual);
    }

    #[test]
    pub fn root() {
        let lexer = Lexer::new("40 + 2");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse().unwrap();
        let expected = Ast::new(Expression::from(ExpressionKind::Binary(
            Box::new(Expression::from(Literal::new(
                LiteralKind::Number(40),
                Location::new(1, 1),
                Span::new(0, 2),
            ))),
            BinaryOperator::new(
                BinaryOperatorKind::Addition,
                Location::new(1, 4),
                Span::new(3, 1),
            ),
            Box::new(Expression::from(Literal::new(
                LiteralKind::Number(2),
                Location::new(1, 6),
                Span::new(5, 1),
            ))),
        )));

        assert_eq!(expected, actual);
        assert_eq!(0, actual.span().start());
        assert_eq!(5, actual.span().end());
    }
}
