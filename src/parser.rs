use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind, UnaryOperator, UnaryOperatorKind};
use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, PeekableLexer, TokenKind};

pub struct Parser<'a> {
    lexer: PeekableLexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer: PeekableLexer::new(lexer, 1),
        }
    }

    pub fn parse(&mut self) -> Result<Ast, Error> {
        let root = self.parse_expression()?;
        Ok(Ast::new(root))
    }

    fn parse_expression(&mut self) -> Result<Expression, Error> {
        self.parse_expression_with_precedence(Precedence::Lowest)
    }

    fn parse_expression_with_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Result<Expression, Error> {
        let token = self.lexer.next()?;

        let mut expression = match token.kind() {
            TokenKind::Number(n) => Expression::from(Literal::new(
                LiteralKind::Number(*n),
                token.location().clone(),
                token.span().clone(),
            )),
            TokenKind::Minus => Expression::new(ExpressionKind::Unary(
                UnaryOperator::new(
                    UnaryOperatorKind::Minus,
                    token.location().clone(),
                    token.span().clone(),
                ),
                Box::new(self.parse_expression_with_precedence(Precedence::Sum)?),
            )),
            TokenKind::OpenParenthesis => {
                let open_loc = token.location();

                let expression = self.parse_expression()?;
                let token = self.lexer.next()?;
                if token.kind() == &TokenKind::CloseParenthesis {
                    expression
                } else {
                    todo!(
                        "parse_expression_with_precedence: error handling {:?}; expected ) for parenthesis open at {}",
                        token.kind(),
                        open_loc
                    )
                }
            }
            _ => todo!(
                "parse_expression_with_precedence: error handling {:?}",
                token.kind()
            ),
        };

        while let Some(next_precedence) = self
            .lexer
            .peek()
            .as_ref()
            .map(|t| Into::<Option<Precedence>>::into(t.kind()))
            .unwrap_or_default()
        {
            if precedence < next_precedence {
                expression = self.parse_infix_expression(expression, next_precedence)?;
            } else {
                break;
            }
        }

        Ok(expression)
    }

    fn parse_infix_expression(
        &mut self,
        left: Expression,
        precedence: Precedence,
    ) -> Result<Expression, Error> {
        let operator = self
            .parse_operator()
            .expect("there must be an operator, we got a precedence");
        let right = self.parse_expression_with_precedence(precedence)?;

        Ok(Expression::new(ExpressionKind::Binary(
            Box::new(left),
            operator,
            Box::new(right),
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
            _ => todo!("parse_literal: error handling {:?}", token.kind()),
        }
    }

    fn parse_operator(&mut self) -> Result<BinaryOperator, Error> {
        let token = self.lexer.next()?;

        match token.kind() {
            TokenKind::Plus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Addition,
                token.location().clone(),
                token.span().clone(),
            )),
            TokenKind::Minus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Subtraction,
                token.location().clone(),
                token.span().clone(),
            )),
            TokenKind::Star => Ok(BinaryOperator::new(
                BinaryOperatorKind::Multiplication,
                token.location().clone(),
                token.span().clone(),
            )),
            TokenKind::Slash => Ok(BinaryOperator::new(
                BinaryOperatorKind::Division,
                token.location().clone(),
                token.span().clone(),
            )),
            _ => todo!("parse_operator: error handling {:?}", token.kind()),
        }
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
enum Precedence {
    Lowest,
    Sum,
    Product,
}

impl From<&TokenKind> for Option<Precedence> {
    fn from(kind: &TokenKind) -> Self {
        match kind {
            TokenKind::Plus => Some(Precedence::Sum),
            TokenKind::Minus => Some(Precedence::Sum),
            TokenKind::Star => Some(Precedence::Product),
            TokenKind::Slash => Some(Precedence::Product),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::{Location, Span};

    #[test]
    pub fn literal() {
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let location = Location::new(1, 1);
        let span = Span::new(0, 2);

        let actual = parser.parse_literal().unwrap();
        let expected = Literal::new(LiteralKind::Number(42), location, span);

        assert_eq!(expected, actual);
    }

    #[test]
    pub fn expression() {
        let lexer = Lexer::new("2 + 20 * 2");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(ExpressionKind::Binary(
            Box::new(Expression::from(Literal::new(
                LiteralKind::Number(2),
                Location::new(1, 1),
                Span::new(0, 1),
            ))),
            BinaryOperator::new(
                BinaryOperatorKind::Addition,
                Location::new(1, 3),
                Span::new(2, 1),
            ),
            Box::new(Expression::from(ExpressionKind::Binary(
                Box::new(Expression::from(Literal::new(
                    LiteralKind::Number(20),
                    Location::new(1, 5),
                    Span::new(4, 2),
                ))),
                BinaryOperator::new(
                    BinaryOperatorKind::Multiplication,
                    Location::new(1, 8),
                    Span::new(7, 1),
                ),
                Box::new(Expression::from(Literal::new(
                    LiteralKind::Number(2),
                    Location::new(1, 10),
                    Span::new(9, 1),
                ))),
            ))),
        ));

        assert_eq!(actual, expected);
    }

    #[test]
    pub fn binary_operator_minus() {
        let lexer = Lexer::new("43 - 1");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expecged = Expression::from(ExpressionKind::Binary(
            Box::new(Expression::from(Literal::new(
                LiteralKind::Number(43),
                Location::new(1, 1),
                Span::new(0, 2),
            ))),
            BinaryOperator::new(
                BinaryOperatorKind::Subtraction,
                Location::new(1, 4),
                Span::new(3, 1),
            ),
            Box::new(Expression::from(Literal::new(
                LiteralKind::Number(1),
                Location::new(1, 6),
                Span::new(5, 1),
            ))),
        ));

        assert_eq!(actual, expecged);
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

        assert_eq!(actual, expected);
        assert_eq!(actual.span().start(), 0);
        assert_eq!(actual.span().end(), 5);
    }

    #[test]
    #[should_panic]
    fn missing_right_parenthesis() {
        let mut parser = Parser::new(Lexer::new("(42"));
        let _ = parser.parse();
    }
}
