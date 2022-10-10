mod ast;

use crate::lexer;
use crate::lexer::{Lexer, Location, Token};
use crate::utils::peekable_iterator::PeekableIterator;
use std::env::set_current_dir;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
pub struct Error { // todo turn into enum
    // todo lexer_error: Option<&'t lexer::Error>,
    pub error: String,
    pub location: Location,
}

impl Error {
    fn err(error: String, location: Location) -> Self {
        Self { error, location }
    }

    fn expected_but_got(expectations: Vec<&str>, received: &Token) -> Self {
        Self::err(
            format!(
                "expected `[{}]`, got `{}`",
                expectations.join("` or `"),
                received
            ),
            received.location().to_owned(),
        )
    }

    fn expected(expectations: Vec<&str>, location: Location) -> Self {
        Self::err(
            format!("expected `{}`, got nothing", expectations.join("` or `")),
            location,
        )
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parsing error: {} at {}", self.error, self.location)
    }
}

impl From<lexer::Error> for Error {
    fn from(e: lexer::Error) -> Self {
        Error::err(e.error, e.location)
    }
}

impl From<&lexer::Error> for Error {
    // todo remove if we keep a ref. to the initial error?
    fn from(e: &lexer::Error) -> Self {
        Error::err(e.error.clone(), e.location.clone())
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug)]
struct Expression {
    location: Location,
    expression: ExpressionKind,
}

impl Expression {
    fn new_identifier(location: Location, name: String) -> Self {
        Self {
            location,
            expression: ExpressionKind::Identifier(name),
        }
    }

    fn new_integer(location: Location, value: u32) -> Self {
        Self {
            location,
            expression: ExpressionKind::Integer(value),
        }
    }

    fn new_binary(left: Expression, operator: Operator, right: Expression) -> Self {
        Self {
            location: left.location.clone(),
            expression: ExpressionKind::Binary(left.into(), operator, right.into()),
        }
    }
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
    Binary(Box<Expression>, Operator, Box<Expression>),
}

impl Display for ExpressionKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                ExpressionKind::Identifier(identifier) => identifier.clone(),
                ExpressionKind::Integer(integer) => format!("{}", integer),
                ExpressionKind::Binary(left, op, right) => format!("({} {} {})", left, op, right),
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
enum OperatorKind {
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

impl OperatorKind {
    fn precedence(&self) -> OperatorPrecedence {
        match *self {
            OperatorKind::And => OperatorPrecedence::Product,
            OperatorKind::Access => OperatorPrecedence::Access,
            OperatorKind::Equals => OperatorPrecedence::Comparison,
            OperatorKind::NotEquals => OperatorPrecedence::Comparison,
            OperatorKind::NotMatches => OperatorPrecedence::Comparison,
            OperatorKind::GreaterThan => OperatorPrecedence::Comparison,
            OperatorKind::GreaterOrEqual => OperatorPrecedence::Comparison,
            OperatorKind::LessThan => OperatorPrecedence::Comparison,
            OperatorKind::LessOrEqual => OperatorPrecedence::Comparison,
            OperatorKind::Subtract => OperatorPrecedence::Sum,
            OperatorKind::Or => OperatorPrecedence::Sum,
            OperatorKind::Reminder => OperatorPrecedence::Product,
            OperatorKind::PrefixCall => OperatorPrecedence::Pipe,
            OperatorKind::Add => OperatorPrecedence::Sum,
            OperatorKind::Divide => OperatorPrecedence::Product,
            OperatorKind::Multiply => OperatorPrecedence::Product,
            OperatorKind::Matches => OperatorPrecedence::Comparison,
        }
    }
}

impl Display for OperatorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            match self {
                OperatorKind::Add => "+",
                OperatorKind::And => "and",
                OperatorKind::Divide => "/",
                OperatorKind::Equals => "==",
                OperatorKind::GreaterOrEqual => ">=",
                OperatorKind::GreaterThan => ">",
                OperatorKind::LessOrEqual => "<=",
                OperatorKind::LessThan => "<",
                OperatorKind::Matches => "~",
                OperatorKind::Multiply => "*",
                OperatorKind::NotEquals => "!=",
                OperatorKind::NotMatches => "!~",
                OperatorKind::Or => "or",
                OperatorKind::PrefixCall => "|",
                OperatorKind::Reminder => "%",
                OperatorKind::Subtract => "-",
                OperatorKind::Access => ".",
            }
        )
    }
}

impl TryFrom<Option<&Token>> for OperatorKind {
    type Error = ();

    fn try_from(token: Option<&Token>) -> std::result::Result<Self, Self::Error> {
        match token {
            Some(&Token::And(_)) => Ok(OperatorKind::And),
            Some(&Token::Dot(_)) => Ok(OperatorKind::Access),
            Some(&Token::EqualEqual(_)) => Ok(OperatorKind::Equals),
            Some(&Token::ExclamEqual(_)) => Ok(OperatorKind::NotEquals),
            Some(&Token::ExclamTilde(_)) => Ok(OperatorKind::NotMatches),
            Some(&Token::Gt(_)) => Ok(OperatorKind::GreaterThan),
            Some(&Token::GtEqual(_)) => Ok(OperatorKind::GreaterOrEqual),
            Some(&Token::Lt(_)) => Ok(OperatorKind::LessThan),
            Some(&Token::LtEqual(_)) => Ok(OperatorKind::LessOrEqual),
            Some(&Token::Minus(_)) => Ok(OperatorKind::Subtract),
            Some(&Token::Or(_)) => Ok(OperatorKind::Or),
            Some(&Token::Percent(_)) => Ok(OperatorKind::Reminder),
            Some(&Token::Pipe(_)) => Ok(OperatorKind::PrefixCall),
            Some(&Token::Plus(_)) => Ok(OperatorKind::Add),
            Some(&Token::Slash(_)) => Ok(OperatorKind::Divide),
            Some(&Token::Star(_)) => Ok(OperatorKind::Multiply),
            Some(&Token::Tilde(_)) => Ok(OperatorKind::Matches),
            _ => Err(()),
        }
    }
}

#[derive(Debug)]
struct Operator {
    location: Location,
    kind: OperatorKind,
}

impl Operator {
    fn precedence(&self) -> OperatorPrecedence {
        self.kind.precedence()
    }
}

impl Display for Operator {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

pub struct Parser<'t> {
    lexer: PeekableIterator<Lexer<'t>>,
    errors: Vec<Error>,
}

impl<'t> Parser<'t> {
    pub fn new(lexer: Lexer<'t>) -> Self {
        Self {
            lexer: lexer.into(),
            errors: Vec::new(),
        }
    }

    /// Returns next valid token, pushes errors if invalid tokens are found on the way.
    fn next_token(&mut self) -> Option<Token> {
        loop {
            match self.lexer.next() {
                Some(Err(error)) => self.errors.push(Error::from(error)),
                Some(Ok(token)) => return Some(token),
                None => return None,
            }
        }
    }

    /// Peeks next valid token. Skipping erroneous token on the way and storing related errors.
    fn peek_token(&mut self) -> Option<&Token> {
        while let Some(Err(e)) = self.lexer.peek() {
            self.errors.push(Error::from(e));
            self.lexer.next();
        }

        self.lexer.peek().map(|t| t.as_ref().unwrap())
    }

    /// Returns the next operator's precedence, if the next token is an operator token; otherwise,
    /// returns `None`
    fn peek_operator_precedence(&mut self) -> Option<OperatorPrecedence> {
        match <Option<&Token> as TryInto<OperatorKind>>::try_into(self.peek_token()) {
            Ok(kind) => Some(kind.precedence()),
            Err(_) => None,
        }
    }

    fn parse_operator(&mut self) -> Option<Operator> {
        match self.peek_token().try_into() {
            Err(_) => None,
            Ok(kind) => Some(Operator {
                location: self.next_token().unwrap().location().to_owned(),
                kind,
            }),
        }
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Result<Expression> {
        let mut expression = match self.next_token() {
            None => return Err(Error::expected(vec!["[Expression]"], Location::new(0, 0))),
            Some(t) => match t {
                Token::Identifier(loc, name) => Expression::new_identifier(loc, name),
                Token::Integer(loc, value) => Expression::new_integer(loc, value),
                t => return Err(Error::expected_but_got(vec!["identifier"], &t)),
            },
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

    fn parse_infix_expression(&mut self, left: Expression) -> Result<Expression> {
        // we're sure there is one as we got a precedence
        let operator = self.parse_operator().unwrap();
        let right = self.parse_expression(operator.precedence())?;
        Ok(Expression::new_binary(left, operator, right))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        add:              "+"   => OperatorKind::Add,
        and:              "and" => OperatorKind::And,
        divide:           "/"   => OperatorKind::Divide,
        equals:           "=="  => OperatorKind::Equals,
        greater_or_equal: ">="  => OperatorKind::GreaterOrEqual,
        greater_than:     ">"   => OperatorKind::GreaterThan,
        less_or_equal:    "<="  => OperatorKind::LessOrEqual,
        less_than:        "<"   => OperatorKind::LessThan,
        matches:          "~"   => OperatorKind::Matches,
        multiply:         "*"   => OperatorKind::Multiply,
        not_equals:       "!="  => OperatorKind::NotEquals,
        not_matches:      "!~"  => OperatorKind::NotMatches,
        or:               "or"  => OperatorKind::Or,
        prefix_call:      "|"   => OperatorKind::PrefixCall,
        reminder:         "%"   => OperatorKind::Reminder,
        subtract:         "-"   => OperatorKind::Subtract,
        suffix_call:      "."   => OperatorKind::Access,
    }

    macro_rules! parse_expression {
        ($($name:ident: $text:expr => $result:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut parser = Parser::new(Lexer::new($text));
                let node = parser.parse_expression(OperatorPrecedence::Lowest);
                let next_node = parser.parse_expression(OperatorPrecedence::Lowest);
                assert!(node.is_ok());
                let node: Expression = node.unwrap();

                assert!(next_node.is_err(), "unexpected expression: {}", next_node.unwrap());

                assert_eq!(format!("{}", node), $result);
            }
        )*
        }
    }

    parse_expression! {
        expression_integer:      "42"                   => "42",
        expression_identifier:   "id"                   => "id",
        expression_binary2:      "1 + 2"                => "(1 + 2)",
        expression_binary3:      "1 + 2 + 3"            => "((1 + 2) + 3)",
        expression_precedence1:  "1 * 2 + 3"            => "((1 * 2) + 3)",
        expression_precedence2:  "1 + 2 * 3"            => "(1 + (2 * 3))",
        expression_infix_call:   "1 + ident.sub * 2"    => "(1 + ((ident . sub) * 2))",
        expression_prefix_call:  "1 == 1 | method"       => "((1 == 1) | method)",
    }
}
