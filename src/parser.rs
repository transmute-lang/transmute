use crate::ast::expression::{ExprId, Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind, UnaryOperator, UnaryOperatorKind};
use crate::ast::statement::{Statement, StatementKind, StmtId};
use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, PeekableLexer, Span, Token, TokenKind};

macro_rules! peek {
    ($parser:ident) => {
        match $parser.lexer.peek() {
            Ok(token) => token,
            Err(_) => Err($parser.lexer.next().unwrap_err())?,
        }
    };
}

pub struct Parser<'s> {
    lexer: PeekableLexer<'s>,
    statements: Vec<Statement<'s>>,
    expressions: Vec<Expression<'s>>,
}

impl<'s> Parser<'s> {
    pub fn new(lexer: Lexer<'s>) -> Self {
        Self {
            lexer: PeekableLexer::new(lexer, 1),
            statements: Vec::new(),
            expressions: Vec::new(),
        }
    }

    pub fn parse(mut self) -> Result<Ast<'s>, Error> {
        let mut statements = Vec::new();
        while let Ok(token) = self.lexer.peek() {
            if token.kind() == &TokenKind::Eof {
                break;
            }

            statements.push(self.parse_statement()?.id());
        }

        Ok(Ast::new(self.expressions, self.statements, statements))
    }

    /// Parses the following:
    /// ```
    /// 'let ident = expr ;
    /// 'let ident ( expr , ... ) = expr ;
    /// 'let ident ( expr , ... ) = { expr ; ... }
    /// 'expr ;
    /// 'ret expr ;
    /// ```
    fn parse_statement(&mut self) -> Result<&Statement<'s>, Error> {
        let token = peek!(self);

        match token.kind() {
            TokenKind::Let => {
                let let_token = self.lexer.next().expect("we just peeked it");
                let identifier_token = self.lexer.next()?;
                let identifier = match identifier_token.kind() {
                    TokenKind::Identifier(ident) => {
                        Identifier::new(ident, identifier_token.span().clone())
                    }
                    _ => todo!(
                        "parse_statement: error handling {:?} at {:?}",
                        identifier_token.kind(),
                        identifier_token.span()
                    ),
                };

                let token = peek!(self);

                if token.kind() == &TokenKind::OpenParenthesis {
                    // let ident '( expr , ... ) = expr ;
                    return self.parse_function(let_token.span(), identifier);
                }

                // let ident = 'expr ;

                // fixme: pattern duplicated several times
                let equal_token = self.lexer.next()?;
                if equal_token.kind() != &TokenKind::Equal {
                    todo!(
                        "parse_statement: error handling {:?}; expected = at {:?}",
                        equal_token.kind(),
                        equal_token.span()
                    )
                }

                let expression = self.parse_expression()?.id();
                let semicolon = self.parse_semicolon()?;
                let span = let_token.span().extend_to(semicolon.span());

                let id = self.push_statement(StatementKind::Let(identifier, expression), span);
                Ok(&self.statements[id.id()])
            }
            TokenKind::Ret => {
                let ret_token = self.lexer.next().expect("we just peeked it");
                let expression = self.parse_expression()?.id();
                let semicolon = self.parse_semicolon()?;
                let span = ret_token.span().extend_to(semicolon.span());

                let id = self.push_statement(StatementKind::Ret(expression), span);
                Ok(&self.statements[id.id()])
            }
            TokenKind::If | TokenKind::While => {
                let expression = self.parse_expression()?;
                let span = expression.span().extend_to(expression.span());
                let id = expression.id();
                let id = self.push_statement(StatementKind::Expression(id), span);
                Ok(&self.statements[id.id()])
            }
            TokenKind::False
            | TokenKind::Identifier(_)
            | TokenKind::Minus
            | TokenKind::Number(_)
            | TokenKind::OpenParenthesis
            | TokenKind::True => {
                let expression = self.parse_expression()?;
                let span = expression.span().clone();
                let expression = expression.id();

                let semicolon = self.parse_semicolon()?;
                let span = span.extend_to(semicolon.span());

                let id = self.push_statement(StatementKind::Expression(expression), span);
                Ok(&self.statements[id.id()])
            }
            _ => todo!(
                "parse_statement: error handling {:?} at {:?}",
                token.kind(),
                token.span()
            ),
        }
    }

    fn push_expression(&mut self, kind: ExpressionKind<'s>, span: Span) -> ExprId {
        let id = ExprId::from(self.expressions.len());
        self.expressions.push(Expression::new(id, kind, span));
        id
    }

    fn push_statement(&mut self, kind: StatementKind<'s>, span: Span) -> StmtId {
        let id = StmtId::from(self.statements.len());
        self.statements.push(Statement::new(id, kind, span));
        id
    }

    /// Parses the following:
    /// ```
    /// let ident '( expr , ... ) = expr ;
    /// let ident '( expr , ... ) = { expr ; ... } ;
    /// ```
    fn parse_function(
        &mut self,
        span: &Span,
        identifier: Identifier<'s>,
    ) -> Result<&Statement<'s>, Error> {
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
                    parameters.push(Identifier::new(ident, token.span().clone()));
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

        let token = peek!(self);

        let (statements, end_span) = if token.kind() == &TokenKind::OpenCurlyBracket {
            // let name ( expr , ... ) = '{ expr ; ... }
            self.lexer.next().expect("we just peeked {");

            let (statements, span) = self.parse_statements()?;

            (statements, span)
        } else {
            // let name ( expr , ... ) = 'expr ;
            let expression = self.parse_expression()?;
            let span = expression.span().clone();
            let expression = expression.id();

            let semicolon_token = self.parse_semicolon()?;
            let end_span = span.extend_to(semicolon_token.span());

            let id = self.push_statement(StatementKind::Expression(expression), end_span.clone());
            (vec![id], end_span)
        };

        let id = self.push_statement(
            StatementKind::LetFn(identifier, parameters, statements),
            span.extend_to(&end_span),
        );
        Ok(&self.statements[id.id()])
    }

    /// Parses the following:
    /// ```
    /// 'expr
    /// ```
    fn parse_expression(&mut self) -> Result<&Expression<'s>, Error> {
        self.parse_expression_with_precedence(Precedence::Lowest)
    }

    fn parse_expression_with_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Result<&Expression<'s>, Error> {
        let token = self.lexer.next()?;

        let mut expression = match token.kind() {
            TokenKind::If => self.parse_if_expression(token.span().clone())?.id(),
            TokenKind::While => self.parse_while_expression(token.span().clone())?.id(),
            TokenKind::Identifier(ident) => {
                let identifier = Identifier::new(ident, token.span().clone());

                let token = peek!(self);

                match *token.kind() {
                    TokenKind::OpenParenthesis => self.parse_function_call(identifier)?.id(),
                    TokenKind::Equal => {
                        self.lexer.next().expect("we just peeked =");
                        let expression = self.parse_expression()?;
                        let span = identifier.span().extend_to(expression.span());
                        let expression = expression.id();
                        self.push_expression(
                            ExpressionKind::Assignment(identifier, expression),
                            span,
                        )
                    }
                    _ => {
                        let span = identifier.span().clone();

                        let literal =
                            Literal::new(LiteralKind::Identifier(identifier), span.clone());

                        self.push_expression(ExpressionKind::Literal(literal), span)
                    }
                }
            }
            TokenKind::Number(n) => {
                let literal = Literal::new(LiteralKind::Number(*n), token.span().clone());
                self.push_expression(ExpressionKind::Literal(literal), token.span().clone())
            }
            TokenKind::Minus => {
                let expression = self.parse_expression_with_precedence(Precedence::Prefix)?;
                let span = token.span().extend_to(expression.span());
                let expression = expression.id();
                self.push_expression(
                    ExpressionKind::Unary(
                        UnaryOperator::new(UnaryOperatorKind::Minus, token.span().clone()),
                        expression,
                    ),
                    span,
                )
            }
            TokenKind::True => self.push_expression(
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(true),
                    token.span().clone(),
                )),
                token.span().clone(),
            ),
            TokenKind::False => self.push_expression(
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(false),
                    token.span().clone(),
                )),
                token.span().clone(),
            ),
            TokenKind::OpenParenthesis => {
                let open_loc = token.span();

                let expression = self.parse_expression()?.id();
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
                expression = self
                    .parse_infix_expression(expression, next_precedence)?
                    .id();
            } else {
                break;
            }
        }

        Ok(&self.expressions[expression.id()])
    }

    /// Parses the following (the if keyword is already consumed):
    /// ```
    /// if expr { expr ; ... } else if expr { expr ; } else { expr ; ... }
    /// ```
    fn parse_if_expression(&mut self, span: Span) -> Result<&Expression<'s>, Error> {
        // if 'expr { expr ; ... } else if expr { expr ; ... } else { expr ; ... }
        let condition = self.parse_expression()?.id();
        let _open_curly_bracket = self.lexer.next()?;
        let (statements, statements_span) = self.parse_statements()?;

        // if expr { expr ; ... } 'else if expr { expr ; ... } else { expr ; ... }
        let (else_branch, else_branch_span) = if self
            .lexer
            .peek()
            .map(|t| t.kind() == &TokenKind::Else)
            .unwrap_or_default()
        {
            let _else_token = self.lexer.next()?; // we consume the else
            let token = self.lexer.next()?;
            match token.kind() {
                TokenKind::If => {
                    // if expr { expr ; ... } else if 'expr { expr ; ... } else { expr ; ... }
                    let expression = self.parse_if_expression(token.span().clone())?;
                    let span = expression.span().clone();
                    let id = expression.id();
                    (
                        vec![self.push_statement(StatementKind::Expression(id), span.clone())],
                        span,
                    )
                }
                // if expr { expr ; ... } 'else { expr ; ... }
                TokenKind::OpenCurlyBracket => self.parse_statements()?,
                _ => todo!(
                    "parse_if_expression: error handling {:?} at {:?}",
                    token.kind(),
                    token.span()
                ),
            }
        } else {
            // if expr { expr ; ... } '
            (vec![], statements_span)
        };

        let span = span.extend_to(&else_branch_span);

        let id = self.push_expression(
            ExpressionKind::If(condition, statements, else_branch),
            span,
        );
        Ok(&self.expressions[id.id()])
    }

    fn parse_while_expression(&mut self, span: Span) -> Result<&Expression<'s>, Error> {
        // while 'expr { expr ; ... }
        let condition = self.parse_expression()?.id();
        let _open_curly_bracket = self.lexer.next()?;
        let (statements, statements_span) = self.parse_statements()?;

        let id = self.push_expression(
            ExpressionKind::While(condition, statements),
            span.extend_to(&statements_span),
        );
        Ok(&self.expressions[id.id()])
    }

    /// Parses the following:
    /// ```
    /// identifier ( expr , ... )
    /// ```
    fn parse_function_call(
        &mut self,
        identifier: Identifier<'s>,
    ) -> Result<&Expression<'s>, Error> {
        // identifier '( expr , ... )
        let open_parenthesis_token = self.lexer.next()?;
        assert_eq!(open_parenthesis_token.kind(), &TokenKind::OpenParenthesis);

        let mut arguments = Vec::new();
        let mut comma_seen = true;

        let span = loop {
            let token = peek!(self);
            match *token.kind() {
                TokenKind::CloseParenthesis => {
                    let token = self.lexer.next().expect("we just peeked it");
                    break identifier.span().extend_to(token.span());
                }
                TokenKind::Comma if !comma_seen => {
                    self.lexer.next().expect("we just peeked ,");
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
                    arguments.push(self.parse_expression()?.id());
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

        let id = self.push_expression(ExpressionKind::FunctionCall(identifier, arguments), span);
        Ok(&self.expressions[id.id()])
    }

    fn parse_infix_expression(
        &mut self,
        left: ExprId,
        precedence: Precedence,
    ) -> Result<&Expression<'s>, Error> {
        let operator = self
            .parse_operator()
            .expect("there must be an operator, we got a precedence");

        let left_span = self.expressions[left.id()].span().clone();

        let right = self.parse_expression_with_precedence(precedence)?;
        let span = left_span.extend_to(right.span());

        let id = right.id();
        let id = self.push_expression(ExpressionKind::Binary(left, operator, id), span);

        Ok(&self.expressions[id.id()])
    }

    fn parse_operator(&mut self) -> Result<BinaryOperator, Error> {
        let token = self.lexer.next()?;

        match token.kind() {
            TokenKind::EqualEqual => Ok(BinaryOperator::new(
                BinaryOperatorKind::Equality,
                token.span().clone(),
            )),
            TokenKind::ExclaimEqual => Ok(BinaryOperator::new(
                BinaryOperatorKind::NonEquality,
                token.span().clone(),
            )),
            TokenKind::Greater => Ok(BinaryOperator::new(
                BinaryOperatorKind::GreaterThan,
                token.span().clone(),
            )),
            TokenKind::GreaterEqual => Ok(BinaryOperator::new(
                BinaryOperatorKind::GreaterThanOrEqualTo,
                token.span().clone(),
            )),
            TokenKind::Smaller => Ok(BinaryOperator::new(
                BinaryOperatorKind::SmallerThan,
                token.span().clone(),
            )),
            TokenKind::SmallerEqual => Ok(BinaryOperator::new(
                BinaryOperatorKind::SmallerThanOrEqualTo,
                token.span().clone(),
            )),
            TokenKind::Minus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Subtraction,
                token.span().clone(),
            )),
            TokenKind::Plus => Ok(BinaryOperator::new(
                BinaryOperatorKind::Addition,
                token.span().clone(),
            )),
            TokenKind::Slash => Ok(BinaryOperator::new(
                BinaryOperatorKind::Division,
                token.span().clone(),
            )),
            TokenKind::Star => Ok(BinaryOperator::new(
                BinaryOperatorKind::Multiplication,
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

impl<'s> Parser<'s> {
    fn parse_semicolon(&mut self) -> Result<Token, Error> {
        let token = self.lexer.next()?;
        if token.kind() == &TokenKind::Semicolon {
            Ok(token)
        } else {
            Err(Error::ExpectedSemicolon(token.span().clone()))
        }
    }

    fn parse_statements(&mut self) -> Result<(Vec<StmtId>, Span), Error> {
        let mut statements = Vec::new();
        loop {
            let token = peek!(self);
            match token.kind() {
                TokenKind::CloseCurlyBracket => {
                    let token = self.lexer.next().expect("we just peeked it");
                    // not the whole span, the last token's span, which is good enough as we
                    // only want to know where the statements end
                    return Ok((statements, token.span().clone()));
                }
                _ => {
                    statements.push(self.parse_statement()?.id());
                }
            }
        }
    }
}

#[derive(Debug, Ord, PartialOrd, Eq, PartialEq)]
// do not reorder!
enum Precedence {
    Lowest,
    Comparison,
    Sum,
    Product,
    Prefix,
}

impl From<&TokenKind<'_>> for Option<Precedence> {
    fn from(kind: &TokenKind) -> Self {
        match kind {
            TokenKind::EqualEqual => Some(Precedence::Comparison),
            TokenKind::ExclaimEqual => Some(Precedence::Comparison),
            TokenKind::Greater => Some(Precedence::Comparison),
            TokenKind::GreaterEqual => Some(Precedence::Comparison),
            TokenKind::Minus => Some(Precedence::Sum),
            TokenKind::Plus => Some(Precedence::Sum),
            TokenKind::Slash => Some(Precedence::Product),
            TokenKind::Smaller => Some(Precedence::Comparison),
            TokenKind::SmallerEqual => Some(Precedence::Comparison),
            TokenKind::Star => Some(Precedence::Product),
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
        let mut parser = Parser::new(Lexer::new("42"));

        let actual = parser.parse_expression().unwrap().id();

        let expressions = vec![Expression::new(
            ExprId::from(0),
            ExpressionKind::Literal(Literal::new(LiteralKind::Number(42), Span::new(1, 1, 0, 2))),
            Span::new(1, 1, 0, 2),
        )];

        assert_eq!(actual, ExprId::from(0));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn expression_literal_identifier() {
        let mut parser = Parser::new(Lexer::new("forty_two"));

        let actual = parser.parse_expression().unwrap().id();

        let expressions = vec![Expression::new(
            ExprId::from(0),
            ExpressionKind::Literal(Literal::new(
                LiteralKind::Identifier(Identifier::new("forty_two", Span::new(1, 1, 0, 9))),
                Span::new(1, 1, 0, 9),
            )),
            Span::new(1, 1, 0, 9),
        )];

        assert_eq!(actual, ExprId::from(0));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn expression_literal_boolean() {
        let mut parser = Parser::new(Lexer::new("true"));

        let actual = parser.parse_expression().unwrap().id();

        let expressions = vec![Expression::new(
            ExprId::from(0),
            ExpressionKind::Literal(Literal::new(
                LiteralKind::Boolean(true),
                Span::new(1, 1, 0, 4),
            )),
            Span::new(1, 1, 0, 4),
        )];

        assert_eq!(actual, ExprId::from(0));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn expression() {
        let mut parser = Parser::new(Lexer::new("2 + 20 * 2"));

        let actual = parser.parse_expression().unwrap().id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 1, 0, 1),
                )),
                Span::new(1, 1, 0, 1),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(20),
                    Span::new(1, 5, 4, 2),
                )),
                Span::new(1, 5, 4, 2),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 10, 9, 1),
                )),
                Span::new(1, 10, 9, 1),
            ),
            Expression::new(
                ExprId::from(3),
                ExpressionKind::Binary(
                    ExprId::from(1),
                    BinaryOperator::new(BinaryOperatorKind::Multiplication, Span::new(1, 8, 7, 1)),
                    ExprId::from(2),
                ),
                Span::new(1, 5, 4, 6),
            ),
            Expression::new(
                ExprId::from(4),
                ExpressionKind::Binary(
                    ExprId::from(0),
                    BinaryOperator::new(BinaryOperatorKind::Addition, Span::new(1, 3, 2, 1)),
                    ExprId::from(3),
                ),
                Span::new(1, 1, 0, 10),
            ),
        ];

        assert_eq!(actual, ExprId::from(4));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn binary_operator_minus() {
        let mut parser = Parser::new(Lexer::new("43 - 1"));

        let actual = parser.parse_expression().unwrap().id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(43),
                    Span::new(1, 1, 0, 2),
                )),
                Span::new(1, 1, 0, 2),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(1),
                    Span::new(1, 6, 5, 1),
                )),
                Span::new(1, 6, 5, 1),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Binary(
                    ExprId::from(0),
                    BinaryOperator::new(BinaryOperatorKind::Subtraction, Span::new(1, 4, 3, 1)),
                    ExprId::from(1),
                ),
                Span::new(1, 1, 0, 6),
            ),
        ];

        assert_eq!(actual, ExprId::from(2));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn prefix_minus() {
        let mut parser = Parser::new(Lexer::new("- 40 * 2"));

        let actual = parser.parse_expression().expect("expression is valid").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(40),
                    Span::new(1, 3, 2, 2),
                )),
                Span::new(1, 3, 2, 2),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Unary(
                    UnaryOperator::new(UnaryOperatorKind::Minus, Span::new(1, 1, 0, 1)),
                    ExprId::from(0),
                ),
                Span::new(1, 1, 0, 4),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 8, 7, 1),
                )),
                Span::new(1, 8, 7, 1),
            ),
            Expression::new(
                ExprId::from(3),
                ExpressionKind::Binary(
                    ExprId::from(1),
                    BinaryOperator::new(BinaryOperatorKind::Multiplication, Span::new(1, 6, 5, 1)),
                    ExprId::from(2),
                ),
                Span::new(1, 1, 0, 8),
            ),
        ];

        assert_eq!(actual, ExprId::from(3));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    #[should_panic]
    fn missing_right_parenthesis() {
        let _ = Parser::new(Lexer::new("(42")).parse();
    }

    #[test]
    fn let_statement() {
        let mut parser = Parser::new(Lexer::new("let forty_two = 42;"));

        let actual = parser.parse_statement().expect("statement is valid").id();

        let expressions = vec![Expression::new(
            ExprId::from(0),
            ExpressionKind::Literal(Literal::new(
                LiteralKind::Number(42),
                Span::new(1, 17, 16, 2),
            )),
            Span::new(1, 17, 16, 2),
        )];

        let statements = vec![Statement::new(
            StmtId::from(0),
            StatementKind::Let(
                Identifier::new("forty_two", Span::new(1, 5, 4, 9)),
                ExprId::from(0),
            ),
            Span::new(1, 1, 0, 19),
        )];

        assert_eq!(actual, StmtId::from(0));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }

    #[test]
    fn assignment() {
        let mut parser = Parser::new(Lexer::new("forty_two = 42"));

        let actual = parser.parse_expression().expect("valid expression").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 13, 12, 2),
                )),
                Span::new(1, 13, 12, 2),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Assignment(
                    Identifier::new("forty_two", Span::new(1, 1, 0, 9)),
                    ExprId::from(0),
                ),
                Span::new(1, 1, 0, 14),
            ),
        ];

        assert_eq!(actual, ExprId::from(1));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn two_statements() {
        let parser = Parser::new(Lexer::new("let forty_two = 42; forty_two;"));

        let actual = parser.parse().expect("source is valid");

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 17, 16, 2),
                )),
                Span::new(1, 17, 16, 2),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Identifier(Identifier::new("forty_two", Span::new(1, 21, 20, 9))),
                    Span::new(1, 21, 20, 9),
                )),
                Span::new(1, 21, 20, 9),
            ),
        ];

        let statements = vec![
            Statement::new(
                StmtId::from(0),
                StatementKind::Let(
                    Identifier::new("forty_two", Span::new(1, 5, 4, 9)),
                    ExprId::from(0),
                ),
                Span::new(1, 1, 0, 19),
            ),
            Statement::new(
                StmtId::from(1),
                StatementKind::Expression(ExprId::from(1)),
                Span::new(1, 21, 20, 10),
            ),
        ];

        let expected = Ast::new(
            expressions,
            statements,
            vec![StmtId::from(0), StmtId::from(1)],
        );

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_statement() {
        let parser = Parser::new(Lexer::new("let times_two(a) = a * 2;"));

        let actual = parser.parse().expect("source is valid");

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Identifier(Identifier::new("a", Span::new(1, 20, 19, 1))),
                    Span::new(1, 20, 19, 1),
                )),
                Span::new(1, 20, 19, 1),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 24, 23, 1),
                )),
                Span::new(1, 24, 23, 1),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Binary(
                    ExprId::from(0),
                    BinaryOperator::new(
                        BinaryOperatorKind::Multiplication,
                        Span::new(1, 22, 21, 1),
                    ),
                    ExprId::from(1),
                ),
                Span::new(1, 20, 19, 5),
            ),
        ];

        let statements = vec![
            Statement::new(
                StmtId::from(0),
                StatementKind::Expression(ExprId::from(2)),
                Span::new(1, 20, 19, 6),
            ),
            Statement::new(
                StmtId::from(1),
                StatementKind::LetFn(
                    Identifier::new("times_two", Span::new(1, 5, 4, 9)),
                    vec![Identifier::new("a", Span::new(1, 15, 14, 1))],
                    vec![StmtId::from(0)],
                ),
                Span::new(1, 1, 0, 25),
            ),
        ];

        let expected = Ast::new(expressions, statements, vec![StmtId::from(1)]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_statements() {
        let parser = Parser::new(Lexer::new("let times_two(a) = { a * 2; }"));

        let actual = parser.parse().expect("source is valid");

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Identifier(Identifier::new("a", Span::new(1, 22, 21, 1))),
                    Span::new(1, 22, 21, 1),
                )),
                Span::new(1, 22, 21, 1),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(2),
                    Span::new(1, 26, 25, 1),
                )),
                Span::new(1, 26, 25, 1),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Binary(
                    ExprId::from(0),
                    BinaryOperator::new(
                        BinaryOperatorKind::Multiplication,
                        Span::new(1, 24, 23, 1),
                    ),
                    ExprId::from(1),
                ),
                Span::new(1, 22, 21, 5),
            ),
        ];

        let statements = vec![
            Statement::new(
                StmtId::from(0),
                StatementKind::Expression(ExprId::from(2)),
                Span::new(1, 22, 21, 6),
            ),
            Statement::new(
                StmtId::from(1),
                StatementKind::LetFn(
                    Identifier::new("times_two", Span::new(1, 5, 4, 9)),
                    vec![Identifier::new("a", Span::new(1, 15, 14, 1))],
                    vec![StmtId::from(0)],
                ),
                Span::new(1, 1, 0, 29),
            ),
        ];
        let expected = Ast::new(expressions, statements, vec![StmtId::from(1)]);

        assert_eq!(actual, expected);
    }

    #[test]
    fn function_call() {
        let mut parser = Parser::new(Lexer::new("times_two(21)"));

        let actual = parser.parse_expression().expect("expression is valid").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(21),
                    Span::new(1, 11, 10, 2),
                )),
                Span::new(1, 11, 10, 2),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::FunctionCall(
                    Identifier::new("times_two", Span::new(1, 1, 0, 9)),
                    vec![ExprId::from(0)],
                ),
                Span::new(1, 1, 0, 13),
            ),
        ];

        assert_eq!(actual, ExprId::from(1));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, vec![]);
    }

    #[test]
    fn ret() {
        let mut parser = Parser::new(Lexer::new("ret 42;"));

        let actual = parser.parse_statement().expect("statement is valid").id();

        let expressions = vec![Expression::new(
            ExprId::from(0),
            ExpressionKind::Literal(Literal::new(LiteralKind::Number(42), Span::new(1, 5, 4, 2))),
            Span::new(1, 5, 4, 2),
        )];

        let statements = vec![Statement::new(
            StmtId::from(0),
            StatementKind::Ret(ExprId::from(0)),
            Span::new(1, 1, 0, 7),
        )];

        assert_eq!(actual, StmtId::from(0));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }

    #[test]
    fn if_simple() {
        let mut parser = Parser::new(Lexer::new("if true { 42; }"));

        let actual = parser.parse_expression().expect("valid expression").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(true),
                    Span::new(1, 4, 3, 4),
                )),
                Span::new(1, 4, 3, 4),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 11, 10, 2),
                )),
                Span::new(1, 11, 10, 2),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::If(ExprId::from(0), vec![StmtId::from(0)], vec![]),
                Span::new(1, 1, 0, 15),
            ),
        ];

        let statements = vec![Statement::new(
            StmtId::from(0),
            StatementKind::Expression(ExprId::from(1)),
            Span::new(1, 11, 10, 3),
        )];

        assert_eq!(actual, ExprId::from(2));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }

    #[test]
    fn if_else() {
        let mut parser = Parser::new(Lexer::new("if true { 42; } else { 43; }"));

        let actual = parser.parse_expression().expect("valid expression").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(true),
                    Span::new(1, 4, 3, 4),
                )),
                Span::new(1, 4, 3, 4),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 11, 10, 2),
                )),
                Span::new(1, 11, 10, 2),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(43),
                    Span::new(1, 24, 23, 2),
                )),
                Span::new(1, 24, 23, 2),
            ),
            Expression::new(
                ExprId::from(3),
                ExpressionKind::If(
                    ExprId::from(0),
                    vec![StmtId::from(0)],
                    vec![StmtId::from(1)],
                ),
                Span::new(1, 1, 0, 28),
            ),
        ];

        let statements = vec![
            Statement::new(
                StmtId::from(0),
                StatementKind::Expression(ExprId::from(1)),
                Span::new(1, 11, 10, 3),
            ),
            Statement::new(
                StmtId::from(1),
                StatementKind::Expression(ExprId::from(2)),
                Span::new(1, 24, 23, 3),
            ),
        ];

        assert_eq!(actual, ExprId::from(3));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }

    #[test]
    fn if_else_if_else() {
        let mut parser = Parser::new(Lexer::new(
            "if true { 42; } else if false { 43; } else { 44; }",
        ));

        let actual = parser.parse_expression().expect("valid expression").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(true),
                    Span::new(1, 4, 3, 4),
                )),
                Span::new(1, 4, 3, 4),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 11, 10, 2),
                )),
                Span::new(1, 11, 10, 2),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(false),
                    Span::new(1, 25, 24, 5),
                )),
                Span::new(1, 25, 24, 5),
            ),
            Expression::new(
                ExprId::from(3),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(43),
                    Span::new(1, 33, 32, 2),
                )),
                Span::new(1, 33, 32, 2),
            ),
            Expression::new(
                ExprId::from(4),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(44),
                    Span::new(1, 46, 45, 2),
                )),
                Span::new(1, 46, 45, 2),
            ),
            Expression::new(
                ExprId::from(5),
                ExpressionKind::If(
                    ExprId::from(2),
                    vec![StmtId::from(1)],
                    vec![StmtId::from(2)],
                ),
                Span::new(1, 22, 21, 29),
            ),
            Expression::new(
                ExprId::from(6),
                ExpressionKind::If(
                    ExprId::from(0),
                    vec![StmtId::from(0)],
                    vec![StmtId::from(3)],
                ),
                Span::new(1, 1, 0, 50),
            ),
        ];

        let statements = vec![
            Statement::new(
                StmtId::from(0),
                StatementKind::Expression(ExprId::from(1)),
                Span::new(1, 11, 10, 3),
            ),
            Statement::new(
                StmtId::from(1),
                StatementKind::Expression(ExprId::from(3)),
                Span::new(1, 33, 32, 3),
            ),
            Statement::new(
                StmtId::from(2),
                StatementKind::Expression(ExprId::from(4)),
                Span::new(1, 46, 45, 3),
            ),
            Statement::new(
                StmtId::from(3),
                StatementKind::Expression(ExprId::from(5)),
                Span::new(1, 22, 21, 29),
            ),
        ];

        assert_eq!(actual, ExprId::from(6));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }

    #[test]
    fn while_loop() {
        let mut parser = Parser::new(Lexer::new("while true { 42; }"));
        let actual = parser.parse_expression().expect("valid expression").id();

        let expressions = vec![
            Expression::new(
                ExprId::from(0),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Boolean(true),
                    Span::new(1, 7, 6, 4),
                )),
                Span::new(1, 7, 6, 4),
            ),
            Expression::new(
                ExprId::from(1),
                ExpressionKind::Literal(Literal::new(
                    LiteralKind::Number(42),
                    Span::new(1, 14, 13, 2),
                )),
                Span::new(1, 14, 13, 2),
            ),
            Expression::new(
                ExprId::from(2),
                ExpressionKind::While(ExprId::from(0), vec![StmtId::from(0)]),
                Span::new(1, 1, 0, 18),
            ),
        ];

        let statements = vec![Statement::new(
            StmtId::from(0),
            StatementKind::Expression(ExprId::from(1)),
            Span::new(1, 14, 13, 3),
        )];

        assert_eq!(actual,ExprId::from(2));
        assert_eq!(parser.expressions, expressions);
        assert_eq!(parser.statements, statements);
    }
}
