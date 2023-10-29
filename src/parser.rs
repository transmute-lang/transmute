use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind, UnaryOperator, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind};
use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, Location, PeekableLexer, Span, TokenKind};

pub struct Parser<'a> {
    lexer: PeekableLexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self {
            lexer: PeekableLexer::new(lexer, 16),
        }
    }

    pub fn parse(&mut self) -> Result<Ast, Error> {
        let mut statements = Vec::new();
        while let Ok(token) = self.lexer.peek() {
            if token.kind() == &TokenKind::Eof {
                break;
            }

            statements.push(self.parse_statement()?);
        }

        Ok(Ast::new(statements))
    }

    /// Parses the following:
    /// ```
    /// 'let ident = expr ;
    /// 'let ident = ( expr , ... ) -> expr ;
    /// 'expr ;
    /// ```
    fn parse_statement(&mut self) -> Result<Statement, Error> {
        let token = match self.lexer.peek() {
            Ok(token) => Ok(token),
            Err(_) => Err(self.lexer.next().expect_err("error case")),
        }?;

        match token.kind() {
            TokenKind::Let => {
                let let_token = self.lexer.next()?;
                let identifier_token = self.lexer.next()?;
                let identifier = match identifier_token.kind() {
                    TokenKind::Identifier(ident) => Identifier::new(
                        ident.to_string(),
                        identifier_token.location().clone(),
                        identifier_token.span().clone(),
                    ),
                    _ => todo!(
                        "parse_statement: error handling {:?} at {}",
                        identifier_token.kind(),
                        identifier_token.location()
                    ),
                };

                let equal_token = self.lexer.next()?;
                if equal_token.kind() != &TokenKind::Equal {
                    todo!(
                        "parse_statement: error handling {:?}; expected = at {}",
                        equal_token.kind(),
                        equal_token.location()
                    )
                }

                // let name = '( expr , ... ) -> expr ;
                if let Ok(open_parenthesis_token) = self.lexer.peek() {
                    if open_parenthesis_token.kind() == &TokenKind::OpenParenthesis {
                        if let Some(close_parameters) =
                            self.lexer.peek_until(TokenKind::CloseParenthesis)
                        {
                            // let name = ( expr , ... ) '-> expr ;
                            if let Ok(arrow_token) = self.lexer.peek_nth(close_parameters + 1) {
                                if arrow_token.kind() == &TokenKind::Arrow {
                                    return self.parse_function(
                                        let_token.location(),
                                        let_token.span(),
                                        identifier,
                                    );
                                }
                            }
                        }
                    }
                }

                let expression = self.parse_expression()?;

                let semicolon_token = self.lexer.next()?;
                if semicolon_token.kind() != &TokenKind::Semicolon {
                    todo!(
                        "parse_statement: error handling {:?}; expected = at {}",
                        semicolon_token.kind(),
                        semicolon_token.location()
                    )
                }

                let span = let_token.span().extend_to(semicolon_token.span());
                Ok(Statement::new(
                    StatementKind::Let(identifier, expression),
                    let_token.location().clone(),
                    span,
                ))
            }
            TokenKind::Minus
            | TokenKind::Number(_)
            | TokenKind::OpenParenthesis
            | TokenKind::Identifier(_) => {
                let expression = self.parse_expression()?;
                let semicolon_token = self.lexer.next()?;
                if semicolon_token.kind() != &TokenKind::Semicolon {
                    todo!(
                        "parse_statement: error handling {:?}; expected = at {}",
                        semicolon_token.kind(),
                        semicolon_token.location()
                    )
                }
                let location = expression.location().clone();
                let span = expression.span().extend_to(semicolon_token.span());
                Ok(Statement::new(
                    StatementKind::Expression(expression),
                    location,
                    span,
                ))
            }
            _ => todo!(
                "parse_statement: error handling {:?} at {}",
                token.kind(),
                token.location()
            ),
        }
    }

    /// Parses the following:
    /// ```
    /// let name = '( expr , ... ) -> expr ;
    /// ```
    fn parse_function(
        &mut self,
        location: &Location,
        span: &Span,
        identifier: Identifier,
    ) -> Result<Statement, Error> {
        // let name = '( expr , ... ) -> expr ;
        let open_parenthesis_token = self.lexer.next().expect("present, as we peeked it already");
        assert_eq!(open_parenthesis_token.kind(), &TokenKind::OpenParenthesis);

        let mut parameters = Vec::new();
        let mut comma_seen = true;

        loop {
            let token = self.lexer.next()?;
            match token.kind() {
                TokenKind::CloseParenthesis => {
                    break;
                }
                TokenKind::Identifier(ident) if comma_seen => {
                    parameters.push(Identifier::new(
                        ident.to_string(),
                        token.location().clone(),
                        token.span().clone(),
                    ));
                    comma_seen = false;
                    if let Ok(token) = self.lexer.peek() {
                        if token.kind() == &TokenKind::Comma {
                            self.lexer.next().expect("we just peeked it");
                            comma_seen = true;
                        }
                    }
                }
                _ => todo!(
                    "parse_function: error handling {:?} at {}",
                    token.kind(),
                    token.location()
                ),
            }
        }

        // let name = ( expr , ... ) '-> expr ;
        let token = self.lexer.next()?;
        if token.kind() != &TokenKind::Arrow {
            todo!(
                "parse_function: error handling {:?} at {}",
                token.kind(),
                token.location()
            )
        }

        // let name = (expr, ...) -> 'expr ;
        let expression = self.parse_expression()?;

        let semicolon_token = self.lexer.next()?;
        if semicolon_token.kind() != &TokenKind::Semicolon {
            todo!(
                "parse_statement: error handling {:?}; expected = at {}",
                semicolon_token.kind(),
                semicolon_token.location()
            )
        }

        Ok(Statement::new(
            StatementKind::LetFn(identifier, parameters, expression),
            location.clone(),
            span.extend_to(semicolon_token.span()),
        ))
    }

    /// Parses the following:
    /// ```
    /// 'expr
    /// ```
    fn parse_expression(&mut self) -> Result<Expression, Error> {
        self.parse_expression_with_precedence(Precedence::Lowest)
    }

    fn parse_expression_with_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Result<Expression, Error> {
        let token = self.lexer.next()?;

        let mut expression = match token.kind() {
            TokenKind::Identifier(ident) => Expression::from(Literal::new(
                LiteralKind::Identifier(ident.clone()),
                token.location().clone(),
                token.span().clone(),
            )),
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
                Box::new(self.parse_expression_with_precedence(Precedence::Prefix)?),
            )),
            TokenKind::OpenParenthesis => {
                let open_loc = token.location();

                let expression = self.parse_expression()?;
                let token = self.lexer.next()?;
                if token.kind() == &TokenKind::CloseParenthesis {
                    expression
                } else {
                    todo!(
                        "parse_expression_with_precedence: error handling {:?}; expected ) at {} for parenthesis open at {}",
                        token.kind(),
                        token.location(),
                        open_loc
                    )
                }
            }
            _ => todo!(
                "parse_expression_with_precedence: error handling {:?} at {}",
                token.kind(),
                token.location()
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
            _ => todo!(
                "parse_operator: error handling {:?} at {}",
                token.kind(),
                token.location()
            ),
        }
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
enum Precedence {
    Lowest,
    Sum,
    Product,
    Prefix,
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
    use crate::ast::Ast;
    use crate::lexer::{Location, Span};

    #[test]
    fn expression_literal_number() {
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let location = Location::new(1, 1);
        let span = Span::new(0, 2);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(ExpressionKind::Literal(Literal::new(
            LiteralKind::Number(42),
            location,
            span,
        )));

        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_literal_identifier() {
        let lexer = Lexer::new("forty_two");
        let mut parser = Parser::new(lexer);

        let location = Location::new(1, 1);
        let span = Span::new(0, 9);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(ExpressionKind::Literal(Literal::new(
            LiteralKind::Identifier("forty_two".to_string()),
            location,
            span,
        )));

        assert_eq!(expected, actual);
    }

    #[test]
    fn expression() {
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
            Box::new(Expression::new(ExpressionKind::Binary(
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
    fn binary_operator_minus() {
        let lexer = Lexer::new("43 - 1");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expecged = Expression::new(ExpressionKind::Binary(
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
    fn prefix_minus() {
        let mut parser = Parser::new(Lexer::new("- 40 * 2"));

        let actual = parser.parse_expression().expect("expression is valid");
        let expected = Expression::new(
            ExpressionKind::Binary(
                Box::new(
                    Expression::new(
                        ExpressionKind::Unary(
                            UnaryOperator::new(
                                UnaryOperatorKind::Minus,
                                Location::new(1,1),
                                Span::new(0, 1)
                            ),
                            Box::new(Expression::new(
                                ExpressionKind::Literal(
                                    Literal::new(
                                        LiteralKind::Number(40),
                                        Location::new(1, 3),
                                        Span::new(2, 2)
                                    )
                                )
                            ))
                        )
                    )
                ),
                BinaryOperator::new(
                    BinaryOperatorKind::Multiplication,
                    Location::new(1, 6),
                    Span::new(5, 1)
                ),
                  Box::new(
                      Expression::new(
                          ExpressionKind::Literal(
                              Literal::new(
                                  LiteralKind::Number(2),
                                  Location::new(1, 8),
                                  Span::new(7, 1)
                              )
                          )
                      )
                  )
            )
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn root() {
        let lexer = Lexer::new("40 + 2;");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse().unwrap();
        let expected = Ast::new(vec![Statement::new(
            StatementKind::Expression(Expression::new(ExpressionKind::Binary(
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
            ))),
            Location::new(1, 1),
            Span::new(0, 7),
        )]);

        assert_eq!(actual, expected);
        assert_eq!(actual.span().start(), 0);
        assert_eq!(actual.span().end(), 6);
    }

    #[test]
    #[should_panic]
    fn missing_right_parenthesis() {
        let mut parser = Parser::new(Lexer::new("(42"));
        let _ = parser.parse();
    }

    #[test]
    fn let_statement() {
        let mut parser = Parser::new(Lexer::new("let forty_two = 42;"));

        let actual = parser.parse_statement().expect("statement is valid");
        let expected = Statement::new(
            StatementKind::Let(
                Identifier::new(
                    "forty_two".to_string(),
                    Location::new(1, 5),
                    Span::new(4, 9),
                ),
                Expression::new(ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Location::new(1, 17),
                    Span::new(16, 2),
                ))),
            ),
            Location::new(1, 1),
            Span::new(0, 19),
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn two_statements() {
        let mut parser = Parser::new(Lexer::new("let forty_two = 42; forty_two;"));

        let actual = parser.parse().expect("source is valid");
        let expected = Ast::new(vec![
            Statement::new(
                StatementKind::Let(
                    Identifier::new(
                        "forty_two".to_string(),
                        Location::new(1, 5),
                        Span::new(4, 9),
                    ),
                    Expression::new(ExpressionKind::Literal(Literal::new(
                        LiteralKind::Number(42),
                        Location::new(1, 17),
                        Span::new(16, 2),
                    ))),
                ),
                Location::new(1, 1),
                Span::new(0, 19),
            ),
            Statement::new(
                StatementKind::Expression(Expression::new(ExpressionKind::Literal(Literal::new(
                    LiteralKind::Identifier("forty_two".to_string()),
                    Location::new(1, 21),
                    Span::new(20, 9),
                )))),
                Location::new(1, 21),
                Span::new(20, 10),
            ),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_statement() {
        let mut parser = Parser::new(Lexer::new("let times_two = (a) -> a * 2;"));

        // let c = (a, b) -> { ret 0; }
        // let c = (a, b) -> 0;

        let actual = parser.parse().expect("source is valid");
        let expected = Ast::new(vec![Statement::new(
            StatementKind::LetFn(
                Identifier::new(
                    "times_two".to_string(),
                    Location::new(1, 5),
                    Span::new(4, 9),
                ),
                vec![Identifier::new(
                    "a".to_string(),
                    Location::new(1, 18),
                    Span::new(17, 1),
                )],
                Expression::new(ExpressionKind::Binary(
                    Box::new(Expression::new(ExpressionKind::Literal(Literal::new(
                        LiteralKind::Identifier("a".to_string()),
                        Location::new(1, 24),
                        Span::new(23, 1),
                    )))),
                    BinaryOperator::new(
                        BinaryOperatorKind::Multiplication,
                        Location::new(1, 26),
                        Span::new(25, 1),
                    ),
                    Box::new(Expression::new(ExpressionKind::Literal(Literal::new(
                        LiteralKind::Number(2),
                        Location::new(1, 28),
                        Span::new(27, 1),
                    )))),
                )),
            ),
            Location::new(1, 1),
            Span::new(0, 29),
        )]);

        assert_eq!(actual, expected);
    }
}
