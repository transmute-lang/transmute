use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind, UnaryOperator, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind};
use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, PeekableLexer, Span, TokenKind};

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
    /// 'let ident ( expr , ... ) = expr ;
    /// 'let ident ( expr , ... ) = { expr ; ... }
    /// 'expr ;
    /// 'ret expr ;
    /// ```
    fn parse_statement(&mut self) -> Result<Statement, Error> {
        // fixme: duplicated several times
        let token = match self.lexer.peek() {
            Ok(token) => token,
            Err(_) => Err(self.lexer.next().unwrap_err())?,
        };

        match token.kind() {
            TokenKind::Let => {
                let let_token = self.lexer.next().expect("we just peeked it");
                let identifier_token = self.lexer.next()?;
                let identifier = match identifier_token.kind() {
                    TokenKind::Identifier(ident) => {
                        Identifier::new(ident.to_string(), identifier_token.span().clone())
                    }
                    _ => todo!(
                        "parse_statement: error handling {:?} at {:?}",
                        identifier_token.kind(),
                        identifier_token.span()
                    ),
                };

                let token = match self.lexer.peek() {
                    Ok(token) => token,
                    Err(_) => Err(self.lexer.next().unwrap_err())?,
                };

                if token.kind() == &TokenKind::OpenParenthesis {
                    // let ident '( expr , ... ) = expr ;
                    return self.parse_function(let_token.span(), identifier);
                }

                // fixme: pattern duplicated several times
                let equal_token = self.lexer.next()?;
                if equal_token.kind() != &TokenKind::Equal {
                    todo!(
                        "parse_statement: error handling {:?}; expected = at {:?}",
                        equal_token.kind(),
                        equal_token.span()
                    )
                }

                let expression = self.parse_expression()?;

                // fixme: duplicated several times
                let semicolon_token = self.lexer.next()?;
                if semicolon_token.kind() != &TokenKind::Semicolon {
                    todo!(
                        "parse_statement: error handling {:?}; expected ; at {:?}",
                        semicolon_token.kind(),
                        semicolon_token.span()
                    )
                }

                let span = let_token.span().extend_to(semicolon_token.span());
                Ok(Statement::new(
                    StatementKind::Let(identifier, expression),
                    span,
                ))
            }
            TokenKind::Ret => {
                let ret_token = self.lexer.next().expect("we just peeked it");
                let expression = self.parse_expression()?;
                let semicolon_token = self.lexer.next()?;
                if semicolon_token.kind() != &TokenKind::Semicolon {
                    todo!(
                        "parse_statement: error handling {:?}; expected ; at {:?}",
                        semicolon_token.kind(),
                        semicolon_token.span()
                    )
                }

                Ok(Statement::new(
                    StatementKind::Ret(expression),
                    ret_token.span().extend_to(semicolon_token.span()),
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
                        "parse_statement: error handling {:?}; expected ; at {:?}",
                        semicolon_token.kind(),
                        semicolon_token.span()
                    )
                }
                let span = expression.span().extend_to(semicolon_token.span());
                Ok(Statement::new(StatementKind::Expression(expression), span))
            }
            _ => todo!(
                "parse_statement: error handling {:?} at {:?}",
                token.kind(),
                token.span()
            ),
        }
    }

    /// Parses the following:
    /// ```
    /// let ident '( expr , ... ) = expr ;
    /// let ident '( expr , ... ) = { expr ; ... }
    /// ```
    fn parse_function(&mut self, span: &Span, identifier: Identifier) -> Result<Statement, Error> {
        // let name '( expr , ... ) = expr ;
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
                TokenKind::Comma if !comma_seen => {
                    comma_seen = true;
                }
                TokenKind::Identifier(ident) if comma_seen => {
                    parameters.push(Identifier::new(ident.to_string(), token.span().clone()));
                    comma_seen = false;
                }
                _ => todo!(
                    "parse_function: error handling {:?} at {:?}",
                    token.kind(),
                    token.span()
                ),
            }
        }

        // let name ( expr , ... ) '= expr ;
        let token = self.lexer.next()?;
        if token.kind() != &TokenKind::Equal {
            todo!(
                "parse_function: error handling {:?} at {:?}",
                token.kind(),
                token.span()
            )
        }

        let token = match self.lexer.peek() {
            Ok(token) => token,
            Err(_) => Err(self.lexer.next().unwrap_err())?,
        };

        let (statements, end_span) = if token.kind() == &TokenKind::OpenCurlyBracket {
            // let name ( expr , ... ) = '{ expr ; ... }
            let _open_curly_bracket_token = self.lexer.next().expect("we just peeked it");

            let mut statements = Vec::new();

            let span = loop {
                let token = match self.lexer.peek() {
                    Ok(token) => token,
                    Err(_) => Err(self.lexer.next().unwrap_err())?,
                };
                match token.kind() {
                    TokenKind::CloseCurlyBracket => {
                        let token = self.lexer.next().expect("we just peeked it");
                        break token.span().clone();
                    }
                    _ => {
                        statements.push(self.parse_statement()?);
                    }
                }
            };

            (statements, span)
        } else {
            // let name ( expr , ... ) = 'expr ;
            let expression = self.parse_expression()?;

            let semicolon_token = self.lexer.next()?;
            if semicolon_token.kind() != &TokenKind::Semicolon {
                todo!(
                    "parse_statement: error handling {:?}; expected = at {:?}",
                    semicolon_token.kind(),
                    semicolon_token.span()
                )
            }

            let end_span = expression.span().extend_to(semicolon_token.span());

            (
                vec![Statement::new(
                    StatementKind::Expression(expression),
                    end_span.clone(),
                )],
                end_span,
            )
        };

        Ok(Statement::new(
            StatementKind::LetFn(identifier, parameters, statements),
            span.extend_to(&end_span),
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
            TokenKind::Identifier(ident) => {
                let identifier = Identifier::new(ident.clone(), token.span().clone());

                let token = match self.lexer.peek() {
                    Ok(token) => token,
                    Err(_) => Err(self.lexer.next().unwrap_err())?,
                };

                match token.kind() {
                    &TokenKind::OpenParenthesis => self.parse_function_call(identifier)?,
                    _ => {
                        let span = identifier.span().clone();
                        Expression::from(Literal::new(LiteralKind::Identifier(identifier), span))
                    }
                }
            }
            TokenKind::Number(n) => {
                Expression::from(Literal::new(LiteralKind::Number(*n), token.span().clone()))
            }
            TokenKind::Minus => {
                let expression = self.parse_expression_with_precedence(Precedence::Prefix)?;
                let span = token.span().extend_to(expression.span());
                Expression::new(
                    ExpressionKind::Unary(
                        UnaryOperator::new(UnaryOperatorKind::Minus, token.span().clone()),
                        Box::new(expression),
                    ),
                    span,
                )
            }
            TokenKind::OpenParenthesis => {
                let open_loc = token.span();

                let expression = self.parse_expression()?;
                let token = self.lexer.next()?;
                if token.kind() == &TokenKind::CloseParenthesis {
                    expression
                } else {
                    todo!(
                        "parse_expression_with_precedence: error handling {:?}; expected ) at {:?} for parenthesis open at {:?}",
                        token.kind(),
                        token.span(),
                        open_loc
                    )
                }
            }
            _ => todo!(
                "parse_expression_with_precedence: error handling {:?} at {:?}",
                token.kind(),
                token.span()
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

    /// Parses the following:
    /// ```
    /// identifier ( expr , ... )
    /// ```
    fn parse_function_call(&mut self, identifier: Identifier) -> Result<Expression, Error> {
        // identifier '( expr , ... )
        let open_parenthesis_token = self.lexer.next()?;
        assert_eq!(open_parenthesis_token.kind(), &TokenKind::OpenParenthesis);

        let mut arguments = Vec::new();
        let mut comma_seen = true;

        let span = loop {
            let token = match self.lexer.peek() {
                Ok(token) => token,
                Err(_) => Err(self.lexer.next().unwrap_err())?,
            };
            match *token.kind() {
                TokenKind::CloseParenthesis => {
                    let token = self.lexer.next().expect("we just peeked it");
                    break identifier.span().extend_to(token.span());
                }
                TokenKind::Comma if !comma_seen => {
                    self.lexer.next().expect("we just peeked it");
                    comma_seen = true;
                }
                TokenKind::Comma if comma_seen => {
                    todo!(
                        "parse_function_call: error handling {:?} at {:?}",
                        token.kind(),
                        token.span()
                    )
                }
                _ if comma_seen => {
                    arguments.push(self.parse_expression()?);
                    comma_seen = false;
                }
                _ => todo!(
                    "parse_function_call: error handling {:?} at {:?}",
                    token.kind(),
                    token.span()
                ),
            }
        };

        // identifier ( expr , ... ) '

        Ok(Expression::new(
            ExpressionKind::MethodCall(identifier, arguments),
            span,
        ))
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

        let span = left.span().extend_to(right.span());

        Ok(Expression::new(
            ExpressionKind::Binary(Box::new(left), operator, Box::new(right)),
            span,
        ))
    }

    fn parse_operator(&mut self) -> Result<BinaryOperator, Error> {
        let token = self.lexer.next()?;

        match token.kind() {
            TokenKind::Plus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Addition,
                token.span().clone(),
            )),
            TokenKind::Minus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Subtraction,
                token.span().clone(),
            )),
            TokenKind::Star => Ok(BinaryOperator::new(
                BinaryOperatorKind::Multiplication,
                token.span().clone(),
            )),
            TokenKind::Slash => Ok(BinaryOperator::new(
                BinaryOperatorKind::Division,
                token.span().clone(),
            )),
            _ => todo!(
                "parse_operator: error handling {:?} at {:?}",
                token.kind(),
                token.span()
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
    use crate::lexer::Span;

    #[test]
    fn expression_literal_number() {
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(
            ExpressionKind::Literal(Literal::new(LiteralKind::Number(42), Span::new(1, 1, 0, 2))),
            Span::new(1, 1, 0, 2),
        );

        assert_eq!(expected, actual);
    }

    #[test]
    fn expression_literal_identifier() {
        let mut parser = Parser::new(Lexer::new("forty_two"));

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(
            ExpressionKind::Literal(Literal::new(
                LiteralKind::Identifier(Identifier::new(
                    "forty_two".to_string(),
                    Span::new(1, 1, 0, 9),
                )),
                Span::new(1, 1, 0, 9),
            )),
            Span::new(1, 1, 0, 9),
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn expression() {
        let lexer = Lexer::new("2 + 20 * 2");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(
            ExpressionKind::Binary(
                Box::new(Expression::from(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 1, 0, 1),
                ))),
                BinaryOperator::new(BinaryOperatorKind::Addition, Span::new(1, 3, 2, 1)),
                Box::new(Expression::new(
                    ExpressionKind::Binary(
                        Box::new(Expression::from(Literal::new(
                            LiteralKind::Number(20),
                            Span::new(1, 5, 4, 2),
                        ))),
                        BinaryOperator::new(
                            BinaryOperatorKind::Multiplication,
                            Span::new(1, 8, 7, 1),
                        ),
                        Box::new(Expression::from(Literal::new(
                            LiteralKind::Number(2),
                            Span::new(1, 10, 9, 1),
                        ))),
                    ),
                    Span::new(1, 5, 4, 6),
                )),
            ),
            Span::new(1, 1, 0, 10),
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn binary_operator_minus() {
        let lexer = Lexer::new("43 - 1");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse_expression().unwrap();
        let expected = Expression::new(
            ExpressionKind::Binary(
                Box::new(Expression::from(Literal::new(
                    LiteralKind::Number(43),
                    Span::new(1, 1, 0, 2),
                ))),
                BinaryOperator::new(BinaryOperatorKind::Subtraction, Span::new(1, 4, 3, 1)),
                Box::new(Expression::from(Literal::new(
                    LiteralKind::Number(1),
                    Span::new(1, 6, 5, 1),
                ))),
            ),
            Span::new(1, 1, 0, 6),
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn prefix_minus() {
        let mut parser = Parser::new(Lexer::new("- 40 * 2"));

        let actual = parser.parse_expression().expect("expression is valid");
        let expected = Expression::new(
            ExpressionKind::Binary(
                Box::new(Expression::new(
                    ExpressionKind::Unary(
                        UnaryOperator::new(UnaryOperatorKind::Minus, Span::new(1, 1, 0, 1)),
                        Box::new(Expression::new(
                            ExpressionKind::Literal(Literal::new(
                                LiteralKind::Number(40),
                                Span::new(1, 3, 2, 2),
                            )),
                            Span::new(1, 3, 2, 2),
                        )),
                    ),
                    Span::new(1, 1, 0, 4),
                )),
                BinaryOperator::new(BinaryOperatorKind::Multiplication, Span::new(1, 6, 5, 1)),
                Box::new(Expression::new(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Number(2),
                        Span::new(1, 8, 7, 1),
                    )),
                    Span::new(1, 8, 7, 1),
                )),
            ),
            Span::new(1, 1, 0, 8),
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn root() {
        let lexer = Lexer::new("40 + 2;");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse().unwrap();
        let expected = Ast::new(vec![Statement::new(
            StatementKind::Expression(Expression::new(
                ExpressionKind::Binary(
                    Box::new(Expression::from(Literal::new(
                        LiteralKind::Number(40),
                        Span::new(1, 1, 0, 2),
                    ))),
                    BinaryOperator::new(BinaryOperatorKind::Addition, Span::new(1, 4, 3, 1)),
                    Box::new(Expression::from(Literal::new(
                        LiteralKind::Number(2),
                        Span::new(1, 6, 5, 1),
                    ))),
                ),
                Span::new(1, 1, 0, 6),
            )),
            Span::new(1, 1, 0, 7),
        )]);

        assert_eq!(actual, expected);
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
                Identifier::new("forty_two".to_string(), Span::new(1, 5, 4, 9)),
                Expression::new(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Number(42),
                        Span::new(1, 17, 16, 2),
                    )),
                    Span::new(1, 17, 16, 2),
                ),
            ),
            Span::new(1, 1, 0, 19),
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
                    Identifier::new("forty_two".to_string(), Span::new(1, 5, 4, 9)),
                    Expression::new(
                        ExpressionKind::Literal(Literal::new(
                            LiteralKind::Number(42),
                            Span::new(1, 17, 16, 2),
                        )),
                        Span::new(1, 17, 16, 2),
                    ),
                ),
                Span::new(1, 1, 0, 19),
            ),
            Statement::new(
                StatementKind::Expression(Expression::new(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Identifier(Identifier::new(
                            "forty_two".to_string(),
                            Span::new(1, 21, 20, 9),
                        )),
                        Span::new(1, 21, 20, 9),
                    )),
                    Span::new(1, 21, 20, 9),
                )),
                Span::new(1, 21, 20, 10),
            ),
        ]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_statement() {
        let mut parser = Parser::new(Lexer::new("let times_two(a) = a * 2;"));

        let actual = parser.parse().expect("source is valid");
        let expected = Ast::new(vec![Statement::new(
            StatementKind::LetFn(
                Identifier::new("times_two".to_string(), Span::new(1, 5, 4, 9)),
                vec![Identifier::new("a".to_string(), Span::new(1, 15, 14, 1))],
                vec![Statement::new(
                    StatementKind::Expression(Expression::new(
                        ExpressionKind::Binary(
                            Box::new(Expression::new(
                                ExpressionKind::Literal(Literal::new(
                                    LiteralKind::Identifier(Identifier::new(
                                        "a".to_string(),
                                        Span::new(1, 20, 19, 1),
                                    )),
                                    Span::new(1, 20, 19, 1),
                                )),
                                Span::new(1, 20, 19, 1),
                            )),
                            BinaryOperator::new(
                                BinaryOperatorKind::Multiplication,
                                Span::new(1, 22, 21, 1),
                            ),
                            Box::new(Expression::new(
                                ExpressionKind::Literal(Literal::new(
                                    LiteralKind::Number(2),
                                    Span::new(1, 24, 23, 1),
                                )),
                                Span::new(1, 24, 23, 1),
                            )),
                        ),
                        Span::new(1, 20, 19, 5),
                    )),
                    Span::new(1, 20, 19, 6),
                )],
            ),
            Span::new(1, 1, 0, 25),
        )]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_statements() {
        let mut parser = Parser::new(Lexer::new("let times_two(a) = { a * 2; }"));

        let actual = parser.parse().expect("source is valid");
        let expected = Ast::new(vec![Statement::new(
            StatementKind::LetFn(
                Identifier::new("times_two".to_string(), Span::new(1, 5, 4, 9)),
                vec![Identifier::new("a".to_string(), Span::new(1, 15, 14, 1))],
                vec![Statement::new(
                    StatementKind::Expression(Expression::new(
                        ExpressionKind::Binary(
                            Box::new(Expression::new(
                                ExpressionKind::Literal(Literal::new(
                                    LiteralKind::Identifier(Identifier::new(
                                        "a".to_string(),
                                        Span::new(1, 22, 21, 1),
                                    )),
                                    Span::new(1, 22, 21, 1),
                                )),
                                Span::new(1, 22, 21, 1),
                            )),
                            BinaryOperator::new(
                                BinaryOperatorKind::Multiplication,
                                Span::new(1, 24, 23, 1),
                            ),
                            Box::new(Expression::new(
                                ExpressionKind::Literal(Literal::new(
                                    LiteralKind::Number(2),
                                    Span::new(1, 26, 25, 1),
                                )),
                                Span::new(1, 26, 25, 1),
                            )),
                        ),
                        Span::new(1, 22, 21, 5),
                    )),
                    Span::new(1, 22, 21, 6),
                )],
            ),
            Span::new(1, 1, 0, 29),
        )]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_call() {
        let mut parser = Parser::new(Lexer::new("times_two(21)"));
        let actual = parser.parse_expression().expect("expression is valid");
        let expected = Expression::new(
            ExpressionKind::MethodCall(
                Identifier::new("times_two".to_string(), Span::new(1, 1, 0, 9)),
                vec![Expression::new(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Number(21),
                        Span::new(1, 11, 10, 2),
                    )),
                    Span::new(1, 11, 10, 2),
                )],
            ),
            Span::new(1, 1, 0, 13),
        );
        assert_eq!(actual, expected);
    }

    #[test]
    fn ret() {
        let mut parser = Parser::new(Lexer::new("ret 42;"));
        let actual = parser.parse_statement().expect("statement is valid");
        let expected = Statement::new(
            StatementKind::Ret(Expression::new(
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 5, 4, 2),
                )),
                Span::new(1, 5, 4, 2),
            )),
            Span::new(1, 1, 0, 7),
        );
        assert_eq!(actual, expected);
    }
}
