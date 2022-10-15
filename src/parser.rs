use crate::lexer;
use crate::lexer::{Lexer, Location, Token};
use crate::utils::peekable_iterator::PeekableIterator;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
#[allow(clippy::enum_variant_names)]
pub enum ErrorKind {
    /// The lexer returned an invalid token error.
    InvalidToken(),
    /// We found an unexpected token
    UnexpectedToken(Vec<Token>),
    /// We found an unexpected token while looking for a closing one
    UnmatchedToken { wanted: Token, matching: Token },
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
                        format!("expected one of `{}`", chars.join("`, `"))
                    }
                    lexer::ErrorKind::ExpectedAny() => "expected any character".to_string(),
                    lexer::ErrorKind::Unexpected(c) => format!("invalid character `{}` found", c),
                },
                _ => unreachable!("should never be here"),
            },
            ErrorKind::UnexpectedToken(wanted) => format!(
                "expected {}, got `{:#}`",
                wanted
                    .iter()
                    .map(|t| format!("`{:#}`", t))
                    .collect::<Vec<String>>()
                    .join(" or "),
                self.token
            ),
            ErrorKind::UnmatchedToken { wanted, matching } => format!(
                "expected `{:#}` from matching `{:#}` at {:#}, got `{}`",
                wanted,
                matching,
                matching.location(),
                self.token
            ),
        };
        write!(f, "Parsing error: {} at {}", error, self.token.location())
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
struct Expression {
    location: Location,
    expression: ExpressionKind,
}

impl Display for Expression {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.expression)
    }
}

#[derive(Debug)]
enum ExpressionKind {
    Identifier(String),
    Integer(u32),
    Binary(Box<Expression>, BinaryOperator, Box<Expression>),
    Unary(UnaryOperator, Box<Expression>),
    Call(String, Location, Vec<Expression>),
}

impl Display for ExpressionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExpressionKind::Identifier(identifier) => identifier.clone(),
                ExpressionKind::Integer(integer) => format!("{}", integer),
                ExpressionKind::Binary(left, op, right) =>
                    format!("({} {} {})", left, op.to_string(), right),
                ExpressionKind::Unary(op, expression) =>
                    format!("({}{})", op.to_string(), expression),
                ExpressionKind::Call(method, _, parameters) => {
                    let parameters = parameters
                        .iter()
                        .map(|e| format!("{}", e.expression))
                        .collect::<Vec<String>>()
                        .join(", ");
                    format!("{}({})", method, parameters)
                }
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

pub struct Parser<'t> {
    lexer: PeekableIterator<Lexer<'t>>,
    errors: Vec<Error>,
    eof: Location,
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

    /// Returns the next operator's precedence, if the next token is an operator token; otherwise,
    /// returns `None`.
    fn peek_operator_precedence(&mut self) -> Option<OperatorPrecedence> {
        self.peek_token()
            .and_then(|t| BinaryOperatorKind::from_token(t).map(|o| o.precedence()))
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
                match self.next_token() {
                    Token::RightParenthesis(_) => expression,
                    token => {
                        return Err(Error {
                            kind: ErrorKind::UnmatchedToken {
                                wanted: Token::RightParenthesis(token.location().clone()),
                                matching: left,
                            },
                            token,
                        })
                    }
                }
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
                    expression: ExpressionKind::Identifier(name),
                },
            },
            Token::Integer(loc, value) => Expression {
                location: loc,
                expression: ExpressionKind::Integer(value),
            },
            token => {
                return Err(Error {
                    kind: ErrorKind::UnexpectedToken(vec![
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
            expression: ExpressionKind::Unary(
                operator,
                self.parse_expression_with_precedence(OperatorPrecedence::Prefix)?
                    .into(),
            ),
        })
    }

    /// parses `[(] ( [expression] [,] )* [expression]? [)]`
    fn parse_call_expression(
        &mut self,
        method_name_location: Location,
        method_name: String,
    ) -> Result<Expression> {
        let parenthesis_location = match self.next_token() {
            Token::LeftParenthesis(parenthesis_location) => parenthesis_location,
            token => {
                return Err(Error {
                    kind: ErrorKind::UnexpectedToken(vec![Token::LeftParenthesis(
                        token.location().clone(),
                    )]),
                    token,
                })
            }
        };

        let mut parameters = Vec::new();
        let mut expect_comma = false;
        while let Some(token) = self.peek_token() {
            match token {
                Token::RightParenthesis(_) => break,
                Token::Comma(_) if !parameters.is_empty() => {
                    self.next_token();
                    expect_comma = false;
                    if let Some(Token::RightParenthesis(_)) = self.peek_token() {
                        break;
                    }
                }
                _ => match self.parse_expression() {
                    Ok(expression) => {
                        parameters.push(expression);
                        expect_comma = true;
                    }
                    Err(e) => {
                        return match e {
                            Error {
                                kind: ErrorKind::UnexpectedToken(mut wanted),
                                token,
                            } => {
                                if expect_comma {
                                    wanted.push(Token::Comma(token.location().clone()));
                                }
                                wanted.push(Token::RightParenthesis(token.location().clone()));
                                Err(Error {
                                    kind: ErrorKind::UnexpectedToken(wanted),
                                    token,
                                })
                            }
                            e => Err(e),
                        }
                    }
                },
            }
        }

        match self.next_token() {
            Token::RightParenthesis(_) => (),
            token => {
                return Err(Error {
                    kind: ErrorKind::UnexpectedToken(vec![Token::LeftParenthesis(
                        token.location().clone(),
                    )]),
                    token,
                })
            }
        }

        Ok(Expression {
            location: method_name_location,
            expression: ExpressionKind::Call(method_name, parenthesis_location, parameters),
        })
    }

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression> {
        let operator = self
            .parse_operator()
            .expect("there must be an operator as we got a precedence");
        let right = self.parse_expression_with_precedence(operator.precedence())?;
        Ok(Expression {
            location: left.location.clone(),
            expression: ExpressionKind::Binary(left.into(), operator, right.into()),
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
            "Parsing error: invalid character `&` found at 1:1"
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
            "Parsing error: expected one of `\"`, `\\` at 1:3"
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
        expression_error_1, parse_expression: "1 + *" => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer`, got `*` at 1:5",
        expression_error_2, parse_expression: "%1"    => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer`, got `%` at 1:1",
        expression_error_3, parse_expression: "  "    => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer`, got `EOF` at 1:3",
        expression_error_4, parse_expression: " (1"   => "Parsing error: expected `)` from matching `(` at 1:2, got `EOF` at 1:4",
        expression_error_5, parse_expression: "("     => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer`, got `EOF` at 1:2",
        call_error_1,       parse_expression: "m(a"   => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer` or `,` or `)`, got `EOF` at 1:4",
        call_error_2,       parse_expression: "m(a,"  => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer` or `)`, got `EOF` at 1:5",
        call_error_4,       parse_expression: "m(,"   => "Parsing error: expected `(` or `+` or `-` or `!` or `identifier` or `integer` or `)`, got `,` at 1:3",
    }
}
