use crate::lexer;
use crate::lexer::{Lexer, Location, Token, TokenKind, TokenValue};
use crate::parser::ErrorKind::UnexpectedToken;
use crate::utils::peekable_iterator::PeekableIterator;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
#[allow(clippy::enum_variant_names)]
pub enum ErrorKind {
    /// The lexer returned an invalid token error.
    InvalidToken,
    /// We found an unexpected token
    UnexpectedToken(
        /// All valid tokens kinds
        Vec<TokenKind>,
    ),
    /// We found an unexpected token while looking for a closing one
    UnmatchedToken {
        /// All tokens kinds that could be at that position, expect for the closing one
        valid: Vec<TokenKind>,
        /// The required closing token kind
        closing: TokenKind,
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
            ErrorKind::InvalidToken => match &self.token {
                Token {
                    kind: TokenKind::Invalid,
                    value: TokenValue::Error(error_kind),
                    ..
                } => match error_kind {
                    lexer::ErrorKind::UnterminatedString => "unterminated string".to_string(),
                    lexer::ErrorKind::ExpectedOneOf(chars) => {
                        format!("expected one of '{}'", chars.join("', '"))
                    }
                    lexer::ErrorKind::ExpectedAny => "expected any character".to_string(),
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

#[derive(Debug)]
pub struct Root {
    functions: Functions,
}

type Functions = Vec<Function>;

#[derive(Debug)]
struct Function {
    location: Location,
    name: String,
    // todo give them names/types ...
    parameters: Vec<String>,
    body: Statements,
}

type Statements = Vec<Statement>;

#[derive(Debug)]
struct Statement {
    location: Location,
    kind: StatementKind,
}

impl Statement {
    /// Tokens that may be present if the thing being parsed was a statement
    // todo rename
    fn tokens() -> Vec<TokenKind> {
        use TokenKind::*;
        vec![Fork, Join, LeftBrace, Let, Match, Semicolon]
    }
}

#[derive(Debug)]
enum StatementKind {
    Fail(Expression),
    Fork(Arms),
    Join(Statements),
    Let(String, Expression),
    Match(Expression, Arms),
}

type Arms = Vec<Arm>;

#[derive(Debug)]
struct Arm {
    location: Location,
    condition: Expression,
    statements: Statements,
}

#[derive(Debug)]
struct Expression {
    location: Location,
    kind: ExpressionKind,
}

impl Expression {
    /// Tokens kinds that may be present if the thing being parsed was an expression
    fn token_kinds() -> Vec<TokenKind> {
        use TokenKind::*;
        vec![Exclam, Identifier, Integer, LeftParenthesis, Minus, Plus]
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

#[derive(Debug)]
enum ExpressionKind {
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    Call(String, Vec<Expression>),
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
                ExpressionKind::Call(method, parameters) => {
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

    fn from_token_kind(token_kind: &TokenKind) -> Option<BinaryOperatorKind> {
        use BinaryOperatorKind::*;
        match *token_kind {
            TokenKind::And => Some(And),
            TokenKind::Dot => Some(Access),
            TokenKind::EqualEqual => Some(Equals),
            TokenKind::ExclamEqual => Some(NotEquals),
            TokenKind::ExclamTilde => Some(NotMatches),
            TokenKind::Gt => Some(GreaterThan),
            TokenKind::GtEqual => Some(GreaterOrEqual),
            TokenKind::Lt => Some(LessThan),
            TokenKind::LtEqual => Some(LessOrEqual),
            TokenKind::Minus => Some(Subtract),
            TokenKind::Or => Some(Or),
            TokenKind::Percent => Some(Reminder),
            TokenKind::Pipe => Some(PrefixCall),
            TokenKind::Plus => Some(Add),
            TokenKind::Slash => Some(Divide),
            TokenKind::Star => Some(Multiply),
            TokenKind::Tilde => Some(Matches),
            _ => None,
        }
    }

    /// Tokens kinds that may be present if the thing being parsed was a binary operation
    fn token_kinds() -> Vec<TokenKind> {
        use TokenKind::*;
        vec![
            And,
            Dot,
            EqualEqual,
            ExclamEqual,
            ExclamTilde,
            Gt,
            GtEqual,
            Lt,
            LtEqual,
            Minus,
            Or,
            Percent,
            Pipe,
            Plus,
            Slash,
            Star,
            Tilde,
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
            token @ Token { kind: $token, .. } => Ok(token),
            token => Err(Error {
                kind: ErrorKind::UnexpectedToken(vec![$token]),
                token,
            }),
        }
    };
}

macro_rules! require_matching_token {
    ($self:ident, $token_kind:path, $opening:expr) => {
        match $self.next_token() {
            token @ Token {
                kind: $token_kind, ..
            } => Ok(token),
            token => Err(Error {
                kind: ErrorKind::UnmatchedToken {
                    valid: Vec::new(),
                    closing: $token_kind,
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

    pub fn parse(mut self) -> std::result::Result<Root, Vec<Error>> {
        match self.parse_root() {
            Ok(root) => {
                if self.errors.is_empty() {
                    Ok(root)
                } else {
                    Err(self.errors)
                }
            }
            Err(e) => {
                self.errors.push(e);
                Err(self.errors)
            }
        }
    }

    pub fn errors(&self) -> &Vec<Error> {
        &self.errors
    }

    /// Returns next valid token, pushes errors if invalid tokens are found on the way.
    fn next_token(&mut self) -> Token {
        loop {
            match self.lexer.next() {
                Some(
                    token @ Token {
                        kind: TokenKind::Invalid,
                        ..
                    },
                ) => self.errors.push(Error {
                    token,
                    kind: ErrorKind::InvalidToken,
                }),
                Some(
                    token @ Token {
                        kind: TokenKind::Eof,
                        ..
                    },
                ) => {
                    self.eof = token.location().clone();
                    return token;
                }
                Some(token) => return token,
                None => {
                    return Token {
                        location: self.eof.clone(),
                        kind: TokenKind::Eof,
                        value: TokenValue::None,
                    }
                }
            }
        }
    }

    /// Peeks next valid token. Skipping erroneous token on the way and storing related errors.
    fn peek_token(&mut self) -> Option<&Token> {
        while let Some(Token {
            kind: TokenKind::Invalid,
            ..
        }) = self.lexer.peek()
        {
            // just ignore invalid tokens, they will be caught when we call next_token()
            self.lexer.next();
        }

        self.lexer.peek()
    }

    fn parse_root(&mut self) -> Result<Root> {
        let mut functions = Vec::new();
        loop {
            if let Some(Token {
                kind: TokenKind::Eof,
                ..
            }) = self.peek_token()
            {
                break;
            }
            functions.push(self.parse_function()?);
        }
        Ok(Root { functions })
    }

    fn parse_function(&mut self) -> Result<Function> {
        let location = require_token!(self, TokenKind::Fn)?.location().clone();
        let name = match require_token!(self, TokenKind::Identifier)? {
            Token {
                kind: TokenKind::Identifier,
                value: TokenValue::String(value),
                ..
            } => value,
            _ => unreachable!(
                "Token::Identifier(..) pattern matches as required a Token::Identifier"
            ),
        };

        let open_parenthesis = require_token!(self, TokenKind::LeftParenthesis)?;
        let mut parameters = Vec::new();
        loop {
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::RightParenthesis,
                    ..
                }) => break,
                _ => {
                    match require_token!(self, TokenKind::Identifier) {
                        Ok(Token {
                            kind: TokenKind::Identifier,
                            value: TokenValue::String(value),
                            ..
                        }) => {
                            parameters.push(value);
                        }
                        Ok(_) => unreachable!(
                            "Token::Identifier(..) pattern matches as required a Token::Identifier"
                        ),
                        Err(Error {
                            token,
                            kind: UnexpectedToken(valid),
                        }) => {
                            return Err(Error {
                                kind: ErrorKind::UnmatchedToken {
                                    valid,
                                    closing: TokenKind::RightParenthesis,
                                    opening: open_parenthesis,
                                },
                                token,
                            });
                        }
                        Err(e) => return Err(e),
                    }
                    match self.peek_token() {
                        Some(Token {
                            kind: TokenKind::RightParenthesis,
                            ..
                        }) => break,
                        Some(Token {
                            kind: TokenKind::Comma,
                            ..
                        }) => {
                            self.next_token();
                            if let Some(Token {
                                kind: TokenKind::RightParenthesis,
                                ..
                            }) = self.peek_token()
                            {
                                break;
                            }
                        }
                        _ => {
                            let token = self.next_token();
                            let mut valid = BinaryOperatorKind::token_kinds();
                            valid.push(TokenKind::Comma);
                            return Err(Error {
                                kind: ErrorKind::UnmatchedToken {
                                    valid,
                                    closing: TokenKind::RightParenthesis,
                                    opening: open_parenthesis,
                                },
                                token,
                            });
                        }
                    }
                }
            }
        }
        require_matching_token!(self, TokenKind::RightParenthesis, open_parenthesis)?;

        match self.peek_token() {
            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {}
            _ => {
                let token = self.next_token();
                return Err(Error {
                    kind: UnexpectedToken(vec![TokenKind::LeftBrace]),
                    token,
                });
            }
        };

        Ok(Function {
            location,
            name,
            parameters,
            body: self.parse_statements()?,
        })
    }

    fn parse_statements(&mut self) -> Result<Statements> {
        let opening_brace = match self.peek_token() {
            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => Some(self.next_token()),
            _ => None,
        };

        let mut statements = Vec::new();

        if let Some(opening_brace) = opening_brace {
            loop {
                match self.peek_token() {
                    Some(Token {
                        kind: TokenKind::RightBrace,
                        ..
                    }) => break,
                    Some(Token {
                        kind: TokenKind::Semicolon,
                        ..
                    }) => {
                        // just skip empty statements
                        self.next_token();
                    }
                    None
                    | Some(Token {
                        kind: TokenKind::Eof,
                        ..
                    }) => {
                        // no next token, just report an error. We need a location, next_token()
                        // gives TokenKind::Eof
                        let token = self.next_token();
                        return Err(Error {
                            kind: ErrorKind::UnmatchedToken {
                                valid: Statement::tokens(),
                                closing: TokenKind::RightBrace,
                                opening: opening_brace,
                            },
                            token,
                        });
                    }
                    _ => statements.push(self.parse_statement()?),
                }
            }
            require_matching_token!(self, TokenKind::RightBrace, opening_brace)?;
        } else if let Some(Token {
            kind: TokenKind::Semicolon,
            ..
        }) = self.peek_token()
        {
            self.next_token();
        } else {
            statements.push(self.parse_statement()?);
        }

        Ok(statements)
    }

    fn parse_statement(&mut self) -> Result<Statement> {
        match self.peek_token() {
            Some(Token {
                kind: TokenKind::Fail,
                ..
            }) => self.parse_fail_statement(),
            Some(Token {
                kind: TokenKind::Let,
                ..
            }) => self.parse_let_statement(),
            Some(Token {
                kind: TokenKind::Match,
                ..
            }) => self.parse_match_statement(),
            Some(Token {
                kind: TokenKind::Fork,
                ..
            }) => self.parse_fork_statement(),
            Some(Token {
                kind: TokenKind::Join,
                ..
            }) => self.parse_join_statement(),
            _ => {
                // even if peek_token() returns None, next_token() returns at least Some(Token::Eof)
                let token = self.next_token();
                Err(Error {
                    kind: UnexpectedToken(Statement::tokens()),
                    token,
                })
            }
        }
    }

    /// parses `[Fail] := [fail] [Expression]`
    fn parse_fail_statement(&mut self) -> Result<Statement> {
        let location = require_token!(self, TokenKind::Fail)?.location().clone();
        let expression = self.parse_expression()?;
        match require_token!(self, TokenKind::Semicolon) {
            Ok(_) => {}
            Err(Error {
                token,
                kind: UnexpectedToken(mut valid),
            }) => {
                valid.append(&mut BinaryOperatorKind::token_kinds());
                valid.push(TokenKind::LeftParenthesis);
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
        let location = require_token!(self, TokenKind::Let)?.location().clone();
        let identifier = require_token!(self, TokenKind::Identifier)?;
        require_token!(self, TokenKind::Equal)?;
        let expression = self.parse_expression()?;
        require_token!(self, TokenKind::Semicolon)?;

        let identifier = match identifier {
            Token {
                kind: TokenKind::Identifier,
                value: TokenValue::String(value),
                ..
            } => value,
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
        let match_location = require_token!(self, TokenKind::Match)?.location().clone();
        let expression = self.parse_expression()?;
        require_token!(self, TokenKind::LeftBrace)?;

        let mut arms = Vec::new();
        loop {
            let expression = self.parse_expression()?;
            require_token!(self, TokenKind::EqualGt)?;
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::LeftBrace,
                    ..
                }) => {}
                _ => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: UnexpectedToken(vec![TokenKind::LeftBrace]),
                        token,
                    });
                }
            }
            let statements = self.parse_statements()?;

            arms.push(Arm {
                location: expression.location.clone(),
                condition: expression,
                statements,
            });

            match self.peek_token() {
                None => break,
                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => break,
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    self.next_token();
                    if let Some(Token {
                        kind: TokenKind::RightBrace,
                        ..
                    }) = self.peek_token()
                    {
                        break;
                    }
                }
                Some(_) => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: UnexpectedToken(vec![TokenKind::RightBrace, TokenKind::Comma]),
                        token,
                    });
                }
            }
        }

        require_token!(self, TokenKind::RightBrace)?;

        Ok(Statement {
            location: match_location,
            kind: StatementKind::Match(expression, arms),
        })
    }

    fn parse_fork_statement(&mut self) -> Result<Statement> {
        let fork_location = require_token!(self, TokenKind::Fork)?.location().clone();
        require_token!(self, TokenKind::LeftBrace)?;

        let mut arms = Vec::new();
        loop {
            let expression = self.parse_expression()?;
            require_token!(self, TokenKind::EqualGt)?;
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::LeftBrace,
                    ..
                }) => {}
                _ => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: UnexpectedToken(vec![TokenKind::LeftBrace]),
                        token,
                    });
                }
            }
            let statements = self.parse_statements()?;

            arms.push(Arm {
                location: expression.location.clone(),
                condition: expression,
                statements,
            });

            match self.peek_token() {
                None => break,
                Some(Token {
                    kind: TokenKind::RightBrace,
                    ..
                }) => break,
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    self.next_token();
                    if let Some(Token {
                        kind: TokenKind::RightBrace,
                        ..
                    }) = self.peek_token()
                    {
                        break;
                    }
                }
                Some(_) => {
                    let token = self.next_token();
                    return Err(Error {
                        kind: UnexpectedToken(vec![TokenKind::RightBrace, TokenKind::Comma]),
                        token,
                    });
                }
            }
        }

        require_token!(self, TokenKind::RightBrace)?;

        Ok(Statement {
            location: fork_location,
            kind: StatementKind::Fork(arms),
        })
    }

    fn parse_join_statement(&mut self) -> Result<Statement> {
        let join_location = require_token!(self, TokenKind::Join)?.location().clone();

        match self.peek_token() {
            Some(Token {
                kind: TokenKind::LeftBrace,
                ..
            }) => {}
            _ => {
                let token = self.next_token();
                return Err(Error {
                    kind: UnexpectedToken(vec![TokenKind::LeftBrace]),
                    token,
                });
            }
        }

        Ok(Statement {
            location: join_location,
            kind: StatementKind::Join(self.parse_statements()?),
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
            left @ Token {
                kind: TokenKind::LeftParenthesis,
                ..
            } => {
                let expression = self.parse_expression()?;
                match require_matching_token!(self, TokenKind::RightParenthesis, left) {
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
                        valid.append(&mut BinaryOperatorKind::token_kinds());
                        valid.push(TokenKind::LeftParenthesis);
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
            Token {
                kind: TokenKind::Plus,
                location,
                ..
            } => self.parse_unary_expression(UnaryOperator {
                location,
                kind: UnaryOperatorKind::Positive,
            })?,
            Token {
                kind: TokenKind::Minus,
                location: loc,
                ..
            } => self.parse_unary_expression(UnaryOperator {
                location: loc,
                kind: UnaryOperatorKind::Negative,
            })?,
            Token {
                kind: TokenKind::Exclam,
                location,
                ..
            } => self.parse_unary_expression(UnaryOperator {
                location,
                kind: UnaryOperatorKind::Not,
            })?,
            Token {
                kind: TokenKind::Identifier,
                location,
                value: TokenValue::String(name),
            } => match self.peek_token() {
                Some(Token {
                    kind: TokenKind::LeftParenthesis,
                    ..
                }) => self.parse_call_expression(location, name)?,
                _ => Expression {
                    location,
                    kind: ExpressionKind::Identifier(name),
                },
            },
            Token {
                kind: TokenKind::Integer,
                location,
                value: TokenValue::Integer(value),
            } => Expression {
                location,
                kind: ExpressionKind::Integer(value),
            },
            Token {
                kind: TokenKind::String,
                location: loc,
                value: TokenValue::String(value),
            } => Expression {
                location: loc,
                kind: ExpressionKind::String(value),
            },
            token => {
                return Err(Error {
                    kind: UnexpectedToken(Expression::token_kinds()),
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
        let open_parenthesis = require_token!(self, TokenKind::LeftParenthesis)?;

        let mut parameters = Vec::new();

        loop {
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::RightParenthesis,
                    ..
                }) => break,
                _ => match self.parse_expression() {
                    Ok(expression) => parameters.push(expression),
                    Err(Error {
                        token,
                        kind: UnexpectedToken(valid),
                    }) => {
                        return Err(Error {
                            kind: ErrorKind::UnmatchedToken {
                                valid,
                                closing: TokenKind::RightParenthesis,
                                opening: open_parenthesis,
                            },
                            token,
                        })
                    }
                    Err(e) => return Err(e),
                },
            }
            match self.peek_token() {
                Some(Token {
                    kind: TokenKind::RightParenthesis,
                    ..
                }) => break,
                Some(Token {
                    kind: TokenKind::Comma,
                    ..
                }) => {
                    self.next_token();
                    if let Some(Token {
                        kind: TokenKind::RightParenthesis,
                        ..
                    }) = self.peek_token()
                    {
                        break;
                    }
                }
                _ => {
                    let token = self.next_token();
                    let mut valid = BinaryOperatorKind::token_kinds();
                    valid.push(TokenKind::Comma);
                    return Err(Error {
                        kind: ErrorKind::UnmatchedToken {
                            valid,
                            closing: TokenKind::RightParenthesis,
                            opening: open_parenthesis,
                        },
                        token,
                    });
                }
            }
        }

        match self.next_token() {
            Token {
                kind: TokenKind::RightParenthesis,
                ..
            } => (),
            token => {
                return Err(Error {
                    kind: UnexpectedToken(vec![TokenKind::LeftParenthesis]),
                    token,
                })
            }
        }

        Ok(Expression {
            location: method_name_location,
            kind: ExpressionKind::Call(method_name, parameters),
        })
    }

    /// Returns the next operator's precedence, if the next token is an operator token; otherwise,
    /// returns `None`.
    fn peek_operator_precedence(&mut self) -> Option<OperatorPrecedence> {
        self.peek_token()
            .and_then(|t| BinaryOperatorKind::from_token_kind(&t.kind).map(|o| o.precedence()))
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
            if let Some(operator) = BinaryOperatorKind::from_token_kind(&token.kind) {
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
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::Eof,
                ..
            }
        ));
        let token = parser.next_token();
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::Eof,
                ..
            }
        ));
    }

    #[test]
    fn peek_token_past_eof() {
        let mut parser = Parser::new(Lexer::new(""));
        let token = parser.next_token();
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::Eof,
                ..
            }
        ));
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
    fn parse_statements_none_1() {
        let mut parser = Parser::new(Lexer::new(";"));
        let statements = parser.parse_statements().expect("expected Ok");
        assert_eq!(statements.len(), 0);
    }

    #[test]
    fn parse_statements_none_2() {
        let mut parser = Parser::new(Lexer::new("{}"));
        let statements = parser.parse_statements().expect("expected Ok");
        assert_eq!(statements.len(), 0);
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
        let mut parser = Parser::new(Lexer::new("match variable { value => { fail \"fail\"; } }"));

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
        match arms.remove(0) {
            Arm {
                condition:
                    Expression {
                        kind: ExpressionKind::Identifier(value),
                        ..
                    },
                statements,
                ..
            } => {
                assert_eq!(value, "value");
                assert_eq!(statements.len(), 1);
            }
            arm => {
                assert!(false, "{:?} does not match pattern", arm);
            }
        };
    }

    #[test]
    fn parse_match_statement_trailing_coma() {
        let mut parser = Parser::new(Lexer::new(
            "match variable { value => { fail \"fail\"; }, }",
        ));

        match parser.parse_match_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Match(_, arms),
                ..
            } => assert_eq!(arms.len(), 1),
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
            }
        };
    }

    #[test]
    fn parse_match_statement_multiple_arms() {
        let mut parser = Parser::new(Lexer::new(
            "match variable { value1 => { fail \"fail1\"; }, value2 => { fail \"fail2\"; } }",
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
            Arm {
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
            Arm {
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

    #[test]
    fn parse_fork_statement() {
        let mut parser = Parser::new(Lexer::new("fork { value => { fail \"fail\"; } }"));

        let mut arms = match parser.parse_fork_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Fork(arms),
                ..
            } => arms,
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
                Vec::new()
            }
        };

        assert_eq!(arms.len(), 1);
        match arms.remove(0) {
            Arm {
                condition:
                    Expression {
                        kind: ExpressionKind::Identifier(value),
                        ..
                    },
                statements,
                ..
            } => {
                assert_eq!(value, "value");
                assert_eq!(statements.len(), 1);
            }
            arm => {
                assert!(false, "{:?} does not match pattern", arm);
            }
        };
    }

    #[test]
    fn parse_fork_statement_trailing_coma() {
        let mut parser = Parser::new(Lexer::new("fork { value => { fail \"fail\"; }, }"));

        match parser.parse_fork_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Fork(arms),
                ..
            } => assert_eq!(arms.len(), 1),
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
            }
        };
    }

    #[test]
    fn parse_fork_statement_multiple_arms() {
        let mut parser = Parser::new(Lexer::new(
            "fork { value1 => { fail \"fail1\"; }, value2 => { fail \"fail2\"; } }",
        ));

        let mut arms = match parser.parse_fork_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Fork(arms),
                ..
            } => arms,
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
                Vec::new()
            }
        };

        assert_eq!(arms.len(), 2);
        match arms.remove(0) {
            Arm {
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
            Arm {
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

    #[test]
    fn parse_join_statement() {
        let mut parser = Parser::new(Lexer::new("join { fail \"fail\"; }"));

        match parser.parse_join_statement().expect("expected Ok") {
            Statement {
                kind: StatementKind::Join(mut statements),
                ..
            } => {
                assert_eq!(statements.len(), 1);
                assert!(matches!(
                    statements.remove(0),
                    Statement {
                        kind: StatementKind::Fail(_),
                        ..
                    }
                ));
            }
            stmt => {
                assert!(false, "{:?} does not match pattern", stmt);
            }
        };
    }

    #[test]
    fn parse_function() {
        let mut parser = Parser::new(Lexer::new("fn main() { fail 12; }"));

        let Function {
            name,
            parameters,
            mut body,
            ..
        } = parser.parse_function().expect("expected Ok");
        assert_eq!(name, "main");
        assert!(parameters.is_empty());
        assert_eq!(body.len(), 1);
        assert!(matches!(
            body.remove(0),
            Statement {
                kind: StatementKind::Fail(_),
                ..
            }
        ));
    }

    #[test]
    fn parse_function_parameter() {
        let mut parser = Parser::new(Lexer::new("fn main(p1) { }"));

        let Function {
            mut parameters,
            body,
            ..
        } = parser.parse_function().expect("expected Ok");
        assert!(body.is_empty());
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters.remove(0), "p1");
    }

    #[test]
    fn parse_function_parameter_trailing_comma() {
        let mut parser = Parser::new(Lexer::new("fn main(p1,) { }"));

        let Function { mut parameters, .. } = parser.parse_function().expect("expected Ok");
        assert_eq!(parameters.len(), 1);
        assert_eq!(parameters.remove(0), "p1");
    }

    #[test]
    fn parse_function_parameters() {
        let mut parser = Parser::new(Lexer::new("fn main(p1, p2) { }"));

        let Function { mut parameters, .. } = parser.parse_function().expect("expected Ok");
        assert_eq!(parameters.len(), 2);
        assert_eq!(parameters.remove(0), "p1");
        assert_eq!(parameters.remove(0), "p2");
    }

    #[test]
    fn parse_root() {
        let mut parser = Parser::new(Lexer::new("fn main() {} fn do_stuff() {}"));

        let Root { mut functions } = parser.parse_root().expect("expected Ok");
        assert_eq!(functions.len(), 2);
        assert_eq!(functions.remove(0).name, "main");
        assert_eq!(functions.remove(0).name, "do_stuff");
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
        err_expression_1, parse_expression:      "1 + *"                     => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got '*' at 1:5",
        err_expression_2, parse_expression:      "%1"                        => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got '%' at 1:1",
        err_expression_3, parse_expression:      "  "                        => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:3",
        err_expression_4, parse_expression:      " (a"                       => "Parsing error: expected 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', ')' from matching '(' at 1:2, got 'EOF' at 1:4",
        err_expression_5, parse_expression:      "("                         => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:2",
        err_call_1,       parse_expression:      "m(a"                       => "Parsing error: expected 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', ',', ')' from matching '(' at 1:2, got 'EOF' at 1:4",
        err_call_2,       parse_expression:      "m(a,"                      => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', ')' from matching '(' at 1:2, got 'EOF' at 1:5",
        err_call_4,       parse_expression:      "m(,"                       => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', ')' from matching '(' at 1:2, got ',' at 1:3",
        err_fail_1,       parse_fail_statement:  ""                          => "Parsing error: expected 'fail', got 'EOF' at 1:1",
        err_fail_2,       parse_fail_statement:  "fail"                      => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:5",
        err_fail_3,       parse_fail_statement:  "fail a"                    => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:7",
        err_let_1,        parse_let_statement:   ""                          => "Parsing error: expected 'let', got 'EOF' at 1:1",
        err_let_2,        parse_let_statement:   "let"                       => "Parsing error: expected 'IDENTIFIER', got 'EOF' at 1:4",
        err_let_3,        parse_let_statement:   "let x"                     => "Parsing error: expected '=', got 'EOF' at 1:6",
        err_let_4,        parse_let_statement:   "let x ="                   => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:8",
        err_let_5,        parse_let_statement:   "let x = a"                 => "Parsing error: expected ';', got 'EOF' at 1:10",
        err_match_1,      parse_match_statement: ""                          => "Parsing error: expected 'match', got 'EOF' at 1:1",
        err_match_2,      parse_match_statement: "match"                     => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:6",
        err_match_3,      parse_match_statement: "match a {"                 => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:10",
        err_match_4,      parse_match_statement: "match a { v"               => "Parsing error: expected '=>', got 'EOF' at 1:12",
        err_match_5,      parse_match_statement: "match a { v =>"            => "Parsing error: expected '{', got 'EOF' at 1:15",
        err_match_6,      parse_match_statement: "match a { v => fail"       => "Parsing error: expected '{', got 'fail' at 1:16",
        err_match_7,      parse_match_statement: "match a { v => { fail 1"   => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:24",
        err_match_8,      parse_match_statement: "match a { v => { fail 1; " => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', '}' from matching '{' at 1:16, got 'EOF' at 1:26",
        err_statements_1, parse_statements:      "1;"                        => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', got '1' at 1:1",
        err_statements_2, parse_statements:      "fail 1"                    => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:7",
        err_statements_3, parse_statements:      "{ fail 1"                  => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:9",
        err_statements_4, parse_statements:      "{ fail 1;"                 => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', '}' from matching '{' at 1:1, got 'EOF' at 1:10",
        err_fork_1,       parse_fork_statement:  ""                          => "Parsing error: expected 'fork', got 'EOF' at 1:1",
        err_fork_2,       parse_fork_statement:  "fork"                      => "Parsing error: expected '{', got 'EOF' at 1:5",
        err_fork_3,       parse_fork_statement:  "fork {"                    => "Parsing error: expected '!', 'IDENTIFIER', 'INTEGER', '(', '-', '+', got 'EOF' at 1:7",
        err_fork_4,       parse_fork_statement:  "fork { v"                  => "Parsing error: expected '=>', got 'EOF' at 1:9",
        err_fork_5,       parse_fork_statement:  "fork { v =>"               => "Parsing error: expected '{', got 'EOF' at 1:12",
        err_fork_6,       parse_fork_statement:  "fork { v => fail }"        => "Parsing error: expected '{', got 'fail' at 1:13",
        err_fork_7,       parse_fork_statement:  "fork { v => { fail 1"      => "Parsing error: expected ';', 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', '(', got 'EOF' at 1:21",
        err_fork_8,       parse_fork_statement:  "fork { v => { fail 1;"     => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', '}' from matching '{' at 1:13, got 'EOF' at 1:22",
        err_join_1,       parse_join_statement:  ""                          => "Parsing error: expected 'join', got 'EOF' at 1:1",
        err_join_2,       parse_join_statement:  "join"                      => "Parsing error: expected '{', got 'EOF' at 1:5",
        err_join_3,       parse_join_statement:  "join {"                    => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', '}' from matching '{' at 1:6, got 'EOF' at 1:7",
        err_function_1,   parse_function:        "fn"                        => "Parsing error: expected 'IDENTIFIER', got 'EOF' at 1:3",
        err_function_2,   parse_function:        "fn main"                   => "Parsing error: expected '(', got 'EOF' at 1:8",
        err_function_3,   parse_function:        "fn main ("                 => "Parsing error: expected 'IDENTIFIER', ')' from matching '(' at 1:9, got 'EOF' at 1:10",
        err_function_4,   parse_function:        "fn main (,"                => "Parsing error: expected 'IDENTIFIER', ')' from matching '(' at 1:9, got ',' at 1:10",
        err_function_5,   parse_function:        "fn main (p1"               => "Parsing error: expected 'and', '.', '==', '!=', '!~', '>', '>=', '<', '<=', '-', 'or', '%', '|', '+', '/', '*', '~', ',', ')' from matching '(' at 1:9, got 'EOF' at 1:12",
        err_function_6,   parse_function:        "fn main ()"                => "Parsing error: expected '{', got 'EOF' at 1:11",
        err_function_7,   parse_function:        "fn main () {"              => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', '}' from matching '{' at 1:12, got 'EOF' at 1:13",
        err_function_8,   parse_function:        "fn main () {fn"            => "Parsing error: expected 'fork', 'join', '{', 'let', 'match', ';', got 'fn' at 1:13",
        err_root,         parse_root:            "let "                      => "Parsing error: expected 'fn', got 'let' at 1:1",
    }
}
