use crate::lexer;
use crate::lexer::{Lexer, Location, Token};
use crate::parser::ErrorKind::UnexpectedToken;
use crate::utils::peekable_iterator::PeekableIterator;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
#[allow(clippy::enum_variant_names)]
pub enum ErrorKind {
    /// The lexer returned an invalid token error.
    InvalidToken(),
    /// We found an unexpected token
    UnexpectedToken(
        /// All valid tokens
        Vec<Token>,
    ),
    /// We found an unexpected token while looking for a closing one
    UnmatchedToken {
        /// All tokens that could be at that position, expect for the closing one
        valid: Vec<Token>,
        /// The required closing token
        closing: Token,
        /// The opening token corresponding to the closing one
        opening: Token,
    },
}

#[derive(Debug)]
pub struct Error {
    pub kind: ErrorKind,
    /// The token that caused the error
    pub token: Token,
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let error = match &self.kind {
            ErrorKind::InvalidToken() => match &self.token {
                Token::Invalid(_, error_kind) => match error_kind {
                    lexer::ErrorKind::UnterminatedString() => "unterminated string".to_string(),
                    lexer::ErrorKind::ExpectedOneOf(chars) => {
                        format!("expected one of '{}'", chars.join("', '"))
                    }
                    lexer::ErrorKind::ExpectedAny() => "expected any character".to_string(),
                    lexer::ErrorKind::Unexpected(c) => format!("invalid character '{}' found", c),
                },
                _ => unreachable!("should never be here"),
            },
            ErrorKind::UnexpectedToken(valid) => format!(
                "expected {}, got '{:#}'",
                valid
                    .iter()
                    .map(|t| format!("'{:#}'", t))
                    .collect::<Vec<String>>()
                    .join(", "),
                self.token
            ),
            ErrorKind::UnmatchedToken {
                valid,
                closing,
                opening,
            } => format!(
                "expected {}{}'{:#}' from matching '{:#}' at {:#}, got '{}'",
                valid
                    .iter()
                    .map(|t| format!("'{:#}'", t))
                    .collect::<Vec<String>>()
                    .join(", "),
                if !valid.is_empty() { ", " } else { "" },
                closing,
                opening,
                opening.location(),
                self.token
            ),
        };
        write!(f, "Parsing error: {} at {}", error, self.token.location())
    }
}

type Result<T> = std::result::Result<T, Error>;

type Statements = Vec<Statement>;

#[derive(Debug)]
struct Statement {
    location: Location,
    kind: StatementKind,
}

#[derive(Debug)]
enum StatementKind {
    Fail(Expression),
    Let(String, Expression),
    Match(Expression, Vec<MatchArm>),
}

#[derive(Debug)]
struct MatchArm {
    location: Location,
    condition: Expression,
    statements: Statements,
}

#[derive(Debug)]
struct Expression {
    location: Location,
    kind: ExpressionKind,
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug)]
enum ExpressionKind {
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    Call(String, Location, Vec<Expression>),
    Identifier(String),
    Integer(u32),
    String(String),
    Unary(UnaryOperator, Box<Expression>),
}

impl Display for ExpressionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExpressionKind::Binary(left, op, right) =>
                    format!("({} {} {})", left, op.to_string(), right),
                ExpressionKind::Call(method, _, parameters) => {
                    let parameters = parameters
                        .iter()
                        .map(|e| format!("{}", e.kind))
                        .collect::<Vec<String>>()
                        .join(", ");
                    format!("{}({})", method, parameters)
                }
                ExpressionKind::Identifier(identifier) => identifier.clone(),
                ExpressionKind::Integer(integer) => format!("{}", integer),
                ExpressionKind::String(string) => format!("\"{}\"", string),
                ExpressionKind::Unary(op, expression) =>
                    format!("({}{})", op.to_string(), expression),
            }
        )
    }
}

/// Precedence used when grouping sub-expressions.
#[derive(PartialOrd, Ord, PartialEq, Eq)]
enum OperatorPrecedence {
    /// Base, lowest, precedence. No operator must have this one!
    Lowest,
    /// Precedence of piping operators, such as `|`, etc.
    Pipe,
    /// Precedence of comparison operators, such as `==`, `!=`, `<=`, etc.
    Comparison,
    /// Precedence of sum operators, such as `+`, `-`, `||`, etc.
    Sum,
    /// Precedence of product operators, such as `*`, `/`, `&&`, etc.
    Product,
    /// Precedence of access operators, such as `.`, etc.
    Access,
    /// Precedence of prefix operators, such as `-`, `!`, etc.
    Prefix,
}

#[derive(Debug)]
struct BinaryOperator {
    location: Location,
    kind: BinaryOperatorKind,
}

impl BinaryOperator {
    fn precedence(&self) -> OperatorPrecedence {
        self.kind.precedence()
    }

    fn to_string(&self) -> &str {
        self.kind.to_string()
    }
}

#[derive(Debug)]
enum BinaryOperatorKind {
    Add,
    And,
    Divide,
    Equals,
    GreaterOrEqual,
    GreaterThan,
    LessOrEqual,
    LessThan,
    Matches,
    Multiply,
    NotEquals,
    NotMatches,
    Or,
    PrefixCall,
    Reminder,
    Subtract,
    Access,
}

impl BinaryOperatorKind {
    fn precedence(&self) -> OperatorPrecedence {
        use OperatorPrecedence::*;
        match *self {
            BinaryOperatorKind::And => Product,
            BinaryOperatorKind::Access => Access,
            BinaryOperatorKind::Equals => Comparison,
            BinaryOperatorKind::NotEquals => Comparison,
            BinaryOperatorKind::NotMatches => Comparison,
            BinaryOperatorKind::GreaterThan => Comparison,
            BinaryOperatorKind::GreaterOrEqual => Comparison,
            BinaryOperatorKind::LessThan => Comparison,
            BinaryOperatorKind::LessOrEqual => Comparison,
            BinaryOperatorKind::Subtract => Sum,
            BinaryOperatorKind::Or => Sum,
            BinaryOperatorKind::Reminder => Product,
            BinaryOperatorKind::PrefixCall => Pipe,
            BinaryOperatorKind::Add => Sum,
            BinaryOperatorKind::Divide => Product,
            BinaryOperatorKind::Multiply => Product,
            BinaryOperatorKind::Matches => Comparison,
        }
    }

    fn to_string(&self) -> &str {
        use BinaryOperatorKind::*;
        match *self {
            Add => "+",
            And => "and",
            Divide => "/",
            Equals => "==",
            GreaterOrEqual => ">=",
            GreaterThan => ">",
            LessOrEqual => "<=",
            LessThan => "<",
            Matches => "~",
            Multiply => "*",
            NotEquals => "!=",
            NotMatches => "!~",
            Or => "or",
            PrefixCall => "|",
            Reminder => "%",
            Subtract => "-",
            Access => ".",
        }
    }

    fn from_token(token: &Token) -> Option<BinaryOperatorKind> {
        use BinaryOperatorKind::*;
        match *token {
            Token::And(_) => Some(And),
            Token::Dot(_) => Some(Access),
            Token::EqualEqual(_) => Some(Equals),
            Token::ExclamEqual(_) => Some(NotEquals),
            Token::ExclamTilde(_) => Some(NotMatches),
            Token::Gt(_) => Some(GreaterThan),
            Token::GtEqual(_) => Some(GreaterOrEqual),
            Token::Lt(_) => Some(LessThan),
            Token::LtEqual(_) => Some(LessOrEqual),
            Token::Minus(_) => Some(Subtract),
            Token::Or(_) => Some(Or),
            Token::Percent(_) => Some(Reminder),
            Token::Pipe(_) => Some(PrefixCall),
            Token::Plus(_) => Some(Add),
            Token::Slash(_) => Some(Divide),
            Token::Star(_) => Some(Multiply),
            Token::Tilde(_) => Some(Matches),
            _ => None,
        }
    }

    /// Tokens that may be present if the thing being parsed was a binary operation
    fn tokens(location: &Location) -> Vec<Token> {
        use Token::*;
        vec![
            And(location.clone()),
            Dot(location.clone()),
            EqualEqual(location.clone()),
            ExclamEqual(location.clone()),
            ExclamTilde(location.clone()),
            Gt(location.clone()),
            GtEqual(location.clone()),
            Lt(location.clone()),
            LtEqual(location.clone()),
            Minus(location.clone()),
            Or(location.clone()),
            Percent(location.clone()),
            Pipe(location.clone()),
            Plus(location.clone()),
            Slash(location.clone()),
            Star(location.clone()),
            Tilde(location.clone()),
        ]
    }
}

#[derive(Debug)]
struct UnaryOperator {
    location: Location,
    kind: UnaryOperatorKind,
}

impl UnaryOperator {
    fn to_string(&self) -> &str {
        self.kind.to_string()
    }
}

#[derive(Debug)]
enum UnaryOperatorKind {
    Positive,
    Negative,
    Not,
}

impl UnaryOperatorKind {
    fn to_string(&self) -> &str {
        use UnaryOperatorKind::*;
        match self {
            Positive => "+",
            Negative => "-",
            Not => "!",
        }
    }
}

pub struct Parser<'t> {
    lexer: PeekableIterator<Lexer<'t>>,
    errors: Vec<Error>,
    eof: Location,
}

macro_rules! require_token {
    ($self:ident, $token:path) => {
        match $self.next_token() {
            token @ $token(_) => Ok(token),
            token => Err(Error {
                kind: ErrorKind::UnexpectedToken(vec![$token(token.location().clone())]),
                token,
            }),
        }
    };
    ($self:ident, $token:path, $ex:expr) => {
        match $self.next_token() {
            token @ $token(_, _) => Ok(token),
            token => Err(Error {
                kind: ErrorKind::UnexpectedToken(vec![$token(
                    token.location().clone(),
                    $ex.into(),
                )]),
                token,
            }),
        }
    };
}

macro_rules! require_matching_token {
    ($self:ident, $token:path, $opening:expr) => {
        match $self.next_token() {
            token @ $token(_) => Ok(token),
            token => Err(Error {
                kind: ErrorKind::UnmatchedToken {
                    valid: Vec::new(),
                    closing: $token(token.location().clone()),
                    opening: $opening,
                },
                token,
            }),
        }
    };
}

impl<'t> Parser<'t> {
    pub fn new(lexer: Lexer<'t>) -> Self {
        Self {
            lexer: lexer.into(),
            errors: Vec::new(),
            eof: Location::new(1, 1),
        }
    }

    pub fn errors(&self) -> &Vec<Error> {
        &self.errors
    }

    /// Returns next valid token, pushes errors if invalid tokens are found on the way.
    fn next_token(&mut self) -> Token {
        loop {
            match self.lexer.next() {
                Some(token @ Token::Invalid(_, _)) => self.errors.push(Error {
                    token,
                    kind: ErrorKind::InvalidToken(),
                }),
                Some(token @ Token::Eof(_)) => {
                    self.eof = token.location().clone();
                    return token;
                }
                Some(token) => return token,
                None => return Token::Eof(self.eof.clone()),
            }
        }
    }

    /// Peeks next valid token. Skipping erroneous token on the way and storing related errors.
    fn peek_token(&mut self) -> Option<&Token> {
        while let Some(Token::Invalid(_, _)) = self.lexer.peek() {
            // just ignore invalid tokens, they will be caught when we call `next_token()`
            self.lexer.next();
        }

        self.lexer.peek()
    }

    fn parse_statements(&mut self) -> Result<Statements> {
        let opening_brace = match self.peek_token() {
            Some(Token::LeftBrace(_)) => Some(self.next_token()),
            _ => None,
        };

        let mut statements = vec![self.parse_statement()?];

        if let Some(opening_brace) = opening_brace {
            loop {
                match self.peek_token() {
                    // just skip empty statements
                    Some(Token::Semicolon(_)) => {}
                    Some(Token::RightBrace(_)) => break,
                    _ => match self.parse_statement() {
                        Ok(statement) => statements.push(statement),
                        Err(Error {
                            token,
                            kind: UnexpectedToken(valid),
                        }) => {
                            return Err(Error {
                                kind: ErrorKind::UnmatchedToken {
                                    valid,
                                    closing: Token::RightBrace(token.location().clone()),
                                    opening: opening_brace,
                                },
                                token,
                            })
                        }
                        Err(e) => return Err(e),
                    },
                }
            }
            require_matching_token!(self, Token::RightBrace, opening_brace)?;
        }

        Ok(statements)
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        match self.peek_token() {
            Some(Token::Fail(_)) => self.parse_fail_statement(),
            Some(Token::Let(_)) => self.parse_let_statement(),
            Some(Token::Match(_)) => self.parse_match_statement(),
            _ => {
                // even if peek_token() returns None, next_token() returns at least Some(Token::Eof)
                let token = self.next_token();
                Err(Error {
                    kind: UnexpectedToken(vec![
                        Token::LeftBrace(token.location().clone()),
                        Token::Let(token.location().clone()),
                        Token::Match(token.location().clone()),
                    ]),
                    token,
                })
            }
        }
    }

    /// parses `[Fail] := [fail] [Expression]`
    fn parse_fail_statement(&mut self) -> Result<Statement> {
        let location = require_token!(self, Token::Fail)?.location().clone();
        let expression = self.parse_expression()?;
        match require_token!(self, Token::Semicolon) {
            Ok(_) => {}
            Err(Error {
                token,
                kind: UnexpectedToken(mut valid),
            }) => {
                valid.append(&mut BinaryOperatorKind::tokens(token.location()));
                valid.push(Token::LeftParenthesis(token.location().clone()));
                return Err(Error {
                    kind: UnexpectedToken(valid),
                    token,
                });
            }
            Err(e) => return Err(e),
        };

        Ok(Statement {
            location,
            kind: StatementKind::Fail(expression),
        })
    }

    /// parses `[Let] = [let] [identifier] [=] [Expression]`
    fn parse_let_statement(&mut self) -> Result<Statement> {
        let location = require_token!(self, Token::Let)?.location().clone();
        let identifier = require_token!(self, Token::Identifier, "")?;
        require_token!(self, Token::Equal)?;
        let expression = self.parse_expression()?;
        require_token!(self, Token::Semicolon)?;

        let identifier = match identifier {
            Token::Identifier(_, value) => value,
            _ => unreachable!(
                "Token::Identifier(..) pattern matches as required a Token::Identifier"
            ),
        };

        Ok(Statement {
            location,
            kind: StatementKind::Let(identifier, expression),
        })
    }

    fn parse_match_statement(&mut self) -> Result<Statement> {
        let match_location = require_token!(self, Token::Match)?.location().clone();
        let expression = self.parse_expression()?;
        require_token!(self, Token::LeftBrace)?;

        let mut arms = Vec::new();
        loop {
            let expression = self.parse_expression()?;
            require_token!(self, Token::EqualGt)?;
            let statements = self.parse_statements()?;

            arms.push(MatchArm {
                location: expression.location.clone(),
                condition: expression,
                statements,
            });

            match self.peek_token() {
                None => break,
                Some(Token::RightBrace(_)) => break,
                Some(Token::Comma(_)) => {
                    self.next_token();
                    if let Some(Token::RightBrace(_)) = self.peek_token() {
                        break;
                    }
                }
                Some(_) => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: UnexpectedToken(vec![
                            Token::RightBrace(token.location().clone()),
                            Token::Comma(token.location().clone()),
                        ]),
                        token,
                    });
                }
            }
        }

        require_token!(self, Token::RightBrace)?;

        Ok(Statement {
            location: match_location,
            kind: StatementKind::Match(expression, arms),
        })
    }

    fn parse_expression(&mut self) -> Result<Expression> {
        self.parse_expression_with_precedence(OperatorPrecedence::Lowest)
    }

    fn parse_expression_with_precedence(
        &mut self,
        precedence: OperatorPrecedence,
    ) -> Result<Expression> {
        let mut expression = match self.next_token() {
            left @ Token::LeftParenthesis(_) => {
                let expression = self.parse_expression()?;
                match require_matching_token!(self, Token::RightParenthesis, left) {
                    Ok(_) => {}
                    Err(Error {
                        token,
                        kind:
                            ErrorKind::UnmatchedToken {
                                mut valid,
                                closing,
                                opening,
                            },
                    }) => {
                        valid.append(&mut BinaryOperatorKind::tokens(token.location()));
                        valid.push(Token::LeftParenthesis(token.location().clone()));
                        return Err(Error {
                            kind: ErrorKind::UnmatchedToken {
                                valid,
                                closing,
                                opening,
                            },
                            token,
                        });
                    }
                    Err(e) => return Err(e),
                }
                expression
            }
            Token::Plus(loc) => self.parse_unary_expression(UnaryOperator {
                location: loc,
                kind: UnaryOperatorKind::Positive,
            })?,
            Token::Minus(loc) => self.parse_unary_expression(UnaryOperator {
                location: loc,
                kind: UnaryOperatorKind::Negative,
            })?,
            Token::Exclam(loc) => self.parse_unary_expression(UnaryOperator {
                location: loc,
                kind: UnaryOperatorKind::Not,
            })?,
            Token::Identifier(loc, name) => match self.peek_token() {
                Some(Token::LeftParenthesis(_)) => self.parse_call_expression(loc, name)?,
                _ => Expression {
                    location: loc,
                    kind: ExpressionKind::Identifier(name),
                },
            },
            Token::Integer(loc, value) => Expression {
                location: loc,
                kind: ExpressionKind::Integer(value),
            },
            Token::String(loc, value) => Expression {
                location: loc,
                kind: ExpressionKind::String(value),
            },
            token => {
                return Err(Error {
                    kind: UnexpectedToken(vec![
                        Token::LeftParenthesis(token.location().clone()),
                        Token::Plus(token.location().clone()),
                        Token::Minus(token.location().clone()),
                        Token::Exclam(token.location().clone()),
                        Token::Identifier(token.location().clone(), "".to_string()),
                        Token::Integer(token.location().clone(), 0),
                    ]),
                    token,
                })
            }
        };

        while let Some(next_precedence) = self.peek_operator_precedence() {
            if precedence < next_precedence {
                expression = self.parse_infix_expression(expression)?
            } else {
                break;
            }
        }

        Ok(expression)
    }

    fn parse_unary_expression(&mut self, operator: UnaryOperator) -> Result<Expression> {
        Ok(Expression {
            location: operator.location.clone(),
            kind: ExpressionKind::Unary(
                operator,
                self.parse_expression_with_precedence(OperatorPrecedence::Prefix)?
                    .into(),
            ),
        })
    }

    /// parses `[(] ( [Expression] [,] )* [Expression]? [)]`
    fn parse_call_expression(
        &mut self,
        method_name_location: Location,
        method_name: String,
    ) -> Result<Expression> {
        let open_parenthesis = require_token!(self, Token::LeftParenthesis)?;

        let mut parameters = Vec::new();

        loop {
            match self.peek_token() {
                Some(Token::RightParenthesis(_)) => break,
                _ => match self.parse_expression() {
                    Ok(expression) => parameters.push(expression),
                    Err(Error {
                        token,
                        kind: UnexpectedToken(valid),
                    }) => {
                        return Err(Error {
                            kind: ErrorKind::UnmatchedToken {
                                valid,
                                closing: Token::RightParenthesis(token.location().clone()),
                                opening: open_parenthesis,
                            },
                            token,
                        })
                    }
                    Err(e) => return Err(e),
                },
            }
            match self.peek_token() {
                Some(Token::RightParenthesis(_)) => break,
                Some(Token::Comma(_)) => {
                    self.next_token();
                    if let Some(Token::RightParenthesis(_)) = self.peek_token() {
                        break;
                    }
                }
                _ => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: ErrorKind::UnmatchedToken {
                            valid: vec![
                                Token::And(token.location().clone()),
                                Token::Dot(token.location().clone()),
                                Token::EqualEqual(token.location().clone()),
                                Token::ExclamEqual(token.location().clone()),
                                Token::ExclamTilde(token.location().clone()),
                                Token::Gt(token.location().clone()),
                                Token::GtEqual(token.location().clone()),
                                Token::Lt(token.location().clone()),
                                Token::LtEqual(token.location().clone()),
                                Token::Minus(token.location().clone()),
                                Token::Or(token.location().clone()),
                                Token::Percent(token.location().clone()),
                                Token::Pipe(token.location().clone()),
                                Token::Plus(token.location().clone()),
                                Token::Slash(token.location().clone()),
                                Token::Star(token.location().clone()),
                                Token::Tilde(token.location().clone()),
                                Token::Comma(token.location().clone()),
                            ],
                            closing: Token::RightParenthesis(token.location().clone()),
                            opening: open_parenthesis,
                        },
                        token,
                    });
                }
            }
        }

        match self.next_token() {
            Token::RightParenthesis(_) => (),
            token => {
                return Err(Error {
                    kind: UnexpectedToken(vec![Token::LeftParenthesis(token.location().clone())]),
                    token,
                })
            }
        }

        Ok(Expression {
            location: method_name_location,
            kind: ExpressionKind::Call(
                method_name,
                open_parenthesis.location().clone(),
                parameters,
            ),
        })
    }

    /// Returns the next operator's precedence, if the next token is an operator token; otherwise,
    /// returns `None`.
    fn peek_operator_precedence(&mut self) -> Option<OperatorPrecedence> {
        self.peek_token()
            .and_then(|t| BinaryOperatorKind::from_token(t).map(|o| o.precedence()))
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression> {
        let operator = self
            .parse_operator()
            .expect("there must be an operator as we got a precedence");
        let right = self.parse_expression_with_precedence(operator.precedence())?;
        Ok(Expression {
            location: left.location.clone(),
            kind: ExpressionKind::Binary(left.into(), operator, right.into()),
        })
    }

    fn parse_operator(&mut self) -> Option<BinaryOperator> {
        if let Some(token) = self.peek_token() {
            if let Some(operator) = BinaryOperatorKind::from_token(token) {
                return Some(BinaryOperator {
                    location: self.next_token().location().clone(),
                    kind: operator,
                });
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next_token_past_eof() {
        let mut parser = Parser::new(Lexer::new(""));
        let token = parser.next_token();
        assert!(matches!(token, Token::Eof(_)));
        let token = parser.next_token();
        assert!(matches!(token, Token::Eof(_)));
    }

    #[test]
    fn peek_token_past_eof() {
        let mut parser = Parser::new(Lexer::new(""));
        let token = parser.next_token();
        assert!(matches!(token, Token::Eof(_)));
        let token = parser.peek_token();
        assert!(token.is_none());
    }

    #[test]
    fn lexer_invalid_character() {
        let mut parser = Parser::new(Lexer::new("&"));
        let _ = parser.parse_expression();
        let errors = parser.errors();
        assert_eq!(errors.len(), 1);
        let error = &errors[0];
        assert_eq!(
            format!("{}", error),
            "Parsing error: invalid character '&' found at 1:1"
        );
    }

    #[test]
    fn lexer_expected_characters() {
        let mut parser = Parser::new(Lexer::new("\"\\"));
        let _ = parser.parse_expression();
        let errors = parser.errors();
        assert_eq!(errors.len(), 1);
        let error = &errors[0];
        assert_eq!(
            format!("{}", error),
            "Parsing error: expected one of '\"', '\\' at 1:3"
        );
    }

    #[test]
    fn unterminated_string() {
        let mut parser = Parser::new(Lexer::new("\""));
        let _ = parser.parse_expression();
        let errors = parser.errors();
        assert_eq!(errors.len(), 1);
        let error = &errors[0];
        assert_eq!(
            format!("{}", error),
            "Parsing error: unterminated string at 1:1"
        );
    }

    #[test]
    fn unterminated_block_string() {
        let mut parser = Parser::new(Lexer::new("\"\"\";"));
        let _ = parser.parse_expression();
        let errors = parser.errors();
        assert_eq!(errors.len(), 1);
        let error = &errors[0];
        assert_eq!(
            format!("{}", error),
            "Parsing error: unterminated string at 1:1"
        );
    }

    macro_rules! parse_operator {
        ($($name:ident: $text:expr => $pat:pat,)*) => {
        $(
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($text));
                let node = parser.parse_operator();
                assert!(node.is_some());
                let node = node.unwrap();
                assert!(matches!(node.kind, $pat))
            }
        )*
        }
    }

    parse_operator! {
        add:              "+"   => BinaryOperatorKind::Add,
        and:              "and" => BinaryOperatorKind::And,
        divide:           "/"   => BinaryOperatorKind::Divide,
        equals:           "=="  => BinaryOperatorKind::Equals,
        greater_or_equal: ">="  => BinaryOperatorKind::GreaterOrEqual,
        greater_than:     ">"   => BinaryOperatorKind::GreaterThan,
        less_or_equal:    "<="  => BinaryOperatorKind::LessOrEqual,
        less_than:        "<"   => BinaryOperatorKind::LessThan,
        matches:          "~"   => BinaryOperatorKind::Matches,
        multiply:         "*"   => BinaryOperatorKind::Multiply,
        not_equals:       "!="  => BinaryOperatorKind::NotEquals,
        not_matches:      "!~"  => BinaryOperatorKind::NotMatches,
        or:               "or"  => BinaryOperatorKind::Or,
        prefix_call:      "|"   => BinaryOperatorKind::PrefixCall,
        reminder:         "%"   => BinaryOperatorKind::Reminder,
        subtract:         "-"   => BinaryOperatorKind::Subtract,
        suffix_call:      "."   => BinaryOperatorKind::Access,
    }

    macro_rules! parse_expression {
        ($($name:ident: $text:expr => $result:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($text));
                let node = parser.parse_expression();
                let next_node = parser.parse_expression();
                let node: Expression = node.expect("expression expected, got err");

                assert!(next_node.is_err(), "unexpected expression: {}", next_node.unwrap());

                assert_eq!(format!("{}", node), $result);
            }
        )*
        }
    }

    parse_expression! {
        expression_integer:          "42"                => "42",
        expression_identifier:       "id"                => "id",
        expression_string:           "\"string\""        => "\"string\"",
        expression_binary2:          "1 + 2"             => "(1 + 2)",
        expression_binary3:          "1 + 2 + 3"         => "((1 + 2) + 3)",
        expression_precedence1:      "1 * 2 + 3"         => "((1 * 2) + 3)",
        expression_precedence2:      "1 + 2 * 3"         => "(1 + (2 * 3))",
        expression_parenthesis:      "(1 + 2) * 3"       => "((1 + 2) * 3)",
        expression_infix_call:       "1 + ident.sub * 2" => "(1 + ((ident . sub) * 2))",
        expression_prefix_call:      "1 == 1 | method"   => "((1 == 1) | method)",
        expression_unary_plus:       "+1"                => "(+1)",
        expression_unary_minus:      "-1"                => "(-1)",
        expression_unary_exclam:     "!1"                => "(!1)",
        expression_unary_in_binary1: "-1 + 1"            => "((-1) + 1)",
        expression_unary_in_binary2: "-1.field"          => "((-1) . field)",
        expression_call_par1:        "method()"          => "method()",
        expression_call_par2:        "method(p1)"        => "method(p1)",
        expression_call_par3:        "method(p1,)"       => "method(p1)",
        expression_call_par4:        "method(p1,p2)"     => "method(p1, p2)",
        expression_call_par5:        "method(p1,p2+p3)"  => "method(p1, (p2 + p3))",
        expression_call_par6:        "method(p1,)"       => "method(p1)",
    }

    #[test]
    fn parse_statements_one() {
        let mut parser = Parser::new(Lexer::new("let a = 1;"));
        let mut statements = parser.parse_statements().expect("expected Ok");
        assert_eq!(statements.len(), 1);
        assert!(matches!(
            statements.remove(0),
            Statement {
                kind: StatementKind::Let(_, _),
                ..
            }
        ));
    }

    #[test]
    fn parse_statements_several() {
        let mut parser = Parser::new(Lexer::new("{ let a = 1; fail 2; }"));
        let mut statements = parser.parse_statements().expect("expected Ok");
        assert_eq!(statements.len(), 2);
        assert!(matches!(
            statements.remove(0),
            Statement {
                kind: StatementKind::Let(_, _),
                ..
            }
        ));
        assert!(matches!(
            statements.remove(0),
            Statement {
                kind: StatementKind::Fail(_),
                ..
            }
        ));
    }

    #[test]
    fn parse_fail_statement() {
        let mut parser = Parser::new(Lexer::new("fail \"error\";"));

        match parser.parse_fail_statement().expect("expected Ok") {
            Statement {
                kind:
                    StatementKind::Fail(Expression {
                        kind: ExpressionKind::String(error),
                        ..
                    }),
                ..
            } => assert_eq!(error, "error"),
            stmt => assert!(false, "{:?} does not match pattern", stmt),
        }
    }

    #[test]
    fn parse_let_statement() {
        let mut parser = Parser::new(Lexer::new("let variable = value;"));
        match parser.parse_let_statement().expect("expected Ok") {
            Statement {
                kind:
                    StatementKind::Let(
                        variable,
                        Expression {
                            kind: ExpressionKind::Identifier(value),
                            ..
                        },
                    ),
                ..
            } => {
                assert_eq!(variable, "variable");
                assert_eq!(value, "value");
            }
            stmt => assert!(false, "{:?} does not match pattern", stmt),
        }
    }

    #[test]
    fn parse_match_statement() {
        let mut parser = Parser::new(Lexer::new("match variable { value => fail \"fail\"; }"));

        let mut arms = match parser.parse_match_statement().expect("expected Ok") {
            Statement {
                kind:
                    StatementKind::Match(
                        Expression {
                            kind: ExpressionKind::Identifier(variable),
                            ..
                        },
                        arms,
                    ),
                ..
            } => {
                assert_eq!(variable, "variable");
                arms
            }
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
                Vec::new()
            }
        };

        assert_eq!(arms.len(), 1);
        let statements = match arms.remove(0) {
            MatchArm {
                condition:
                    Expression {
                        kind: ExpressionKind::Identifier(value),
                        ..
                    },
                statements,
                ..
            } => {
                assert_eq!(value, "value");
                statements
            }
            arm => {
                assert!(false, "{:?} does not match pattern", arm);
                Vec::new()
            }
        };

        assert_eq!(statements.len(), 1);
    }

    #[test]
    fn parse_match_statement_trailing_coma() {
        let mut parser = Parser::new(Lexer::new("match variable { value => fail \"fail\";, }"));

        let arms = match parser.parse_match_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Match(_, arms),
                ..
            } => arms,
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
                Vec::new()
            }
        };

        assert_eq!(arms.len(), 1);
    }

    #[test]
    fn parse_match_statement_multiple_arms() {
        let mut parser = Parser::new(Lexer::new(
            "match variable { value1 => fail \"fail1\";, value2 => fail \"fail2\"; }",
        ));

        let mut arms = match parser.parse_match_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Match(_, arms),
                ..
            } => arms,
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
                Vec::new()
            }
        };

        assert_eq!(arms.len(), 2);
        match arms.remove(0) {
            MatchArm {
                condition:
                    Expression {
                        kind: ExpressionKind::Identifier(value),
                        ..
                    },
                ..
            } => {
                assert_eq!(value, "value1");
            }
            arm => {
                assert!(false, "{:?} does not match pattern", arm);
            }
        };
        match arms.remove(0) {
            MatchArm {
                condition:
                    Expression {
                        kind: ExpressionKind::Identifier(value),
                        ..
                    },
                ..
            } => {
                assert_eq!(value, "value2");
            }
            arm => {
                assert!(false, "{:?} does not match pattern", arm);
            }
        };
    }

    macro_rules! parse_error {
        ($($name:ident, $root:ident: $text:expr => $result:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($text));
                let error = parser
                    .$root()
                    .expect_err("err expected, got ok");

                assert_eq!(format!("{}", error), $result);
            }
        )*
        }
    }

    parse_error! {
        expression_error_1, parse_expression:      "1 + *"                   => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got '*' at 1:5",
        expression_error_2, parse_expression:      "%1"                      => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got '%' at 1:1",
        expression_error_3, parse_expression:      "  "                      => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got 'EOF' at 1:3",
        expression_error_4, parse_expression:      " (a"                     => "Parsing error: expected 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', ')' from matching '(' at 1:2, got 'EOF' at 1:4",
        expression_error_5, parse_expression:      "("                       => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got 'EOF' at 1:2",
        call_error_1,       parse_expression:      "m(a"                     => "Parsing error: expected 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', ',', ')' from matching '(' at 1:2, got 'EOF' at 1:4",
        call_error_2,       parse_expression:      "m(a,"                    => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', ')' from matching '(' at 1:2, got 'EOF' at 1:5",
        call_error_4,       parse_expression:      "m(,"                     => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', ')' from matching '(' at 1:2, got ',' at 1:3",
        fail_1,             parse_fail_statement:  "fail"                    => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got 'EOF' at 1:5",
        fail_2,             parse_fail_statement:  "fail a"                  => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:7",
        let_1,              parse_let_statement:   "let"                     => "Parsing error: expected 'identifier', got 'EOF' at 1:4",
        let_2,              parse_let_statement:   "let x"                   => "Parsing error: expected '=', got 'EOF' at 1:6",
        let_3,              parse_let_statement:   "let x ="                 => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got 'EOF' at 1:8",
        let_4,              parse_let_statement:   "let x = a"               => "Parsing error: expected ';', got 'EOF' at 1:10",
        match_1,            parse_match_statement: "match {}"                => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got '{' at 1:7",
        match_2,            parse_match_statement: "match a {}"              => "Parsing error: expected '(', '+', '-', '!', 'identifier', 'integer', got '}' at 1:10",
        match_3,            parse_match_statement: "match a { v }"           => "Parsing error: expected '=>', got '}' at 1:13",
        match_4,            parse_match_statement: "match a { v => }"        => "Parsing error: expected '{', 'let', 'match', got '}' at 1:16",
        match_5,            parse_match_statement: "match a { v => fail 1 }" => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got '}' at 1:23",
        statements_1,       parse_statements:      "1;"                      => "Parsing error: expected '{', 'let', 'match', got 'integer' at 1:1",
        statements_2,       parse_statements:      "fail 1"                  => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:7",
        statements_3,       parse_statements:      "{ fail 1"                => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:9",
        statements_4,       parse_statements:      "{ fail 1;"               => "Parsing error: expected '{', 'let', 'match', '}' from matching '{' at 1:1, got 'EOF' at 1:10",
    }
}
