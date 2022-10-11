use crate::lexer;
use crate::lexer::{Lexer, Location, Token};
use crate::utils::peekable_iterator::PeekableIterator;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug)]
pub struct Error {
    // todo turn into enum
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

impl TryFrom<&Token> for OperatorKind {
    type Error = ();

    fn try_from(token: &Token) -> std::result::Result<Self, Self::Error> {
        use OperatorKind::*;
        match *token {
            Token::And(_) => Ok(And),
            Token::Dot(_) => Ok(Access),
            Token::EqualEqual(_) => Ok(Equals),
            Token::ExclamEqual(_) => Ok(NotEquals),
            Token::ExclamTilde(_) => Ok(NotMatches),
            Token::Gt(_) => Ok(GreaterThan),
            Token::GtEqual(_) => Ok(GreaterOrEqual),
            Token::Lt(_) => Ok(LessThan),
            Token::LtEqual(_) => Ok(LessOrEqual),
            Token::Minus(_) => Ok(Subtract),
            Token::Or(_) => Ok(Or),
            Token::Percent(_) => Ok(Reminder),
            Token::Pipe(_) => Ok(PrefixCall),
            Token::Plus(_) => Ok(Add),
            Token::Slash(_) => Ok(Divide),
            Token::Star(_) => Ok(Multiply),
            Token::Tilde(_) => Ok(Matches),
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

        self.lexer
            .peek()
            .map(|t| t.as_ref().expect("cannot be an error, we weeded them"))
    }

    /// Returns the next operator's precedence, if the next token is an operator token; otherwise,
    /// returns `None`.
    fn peek_operator_precedence(&mut self) -> Option<OperatorPrecedence> {
        self.peek_token()
            .and_then(|t| t.try_into().ok())
            .map(|k: OperatorKind| k.precedence())
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Result<Expression> {
        let mut expression = match self.next_token() {
            None => return Err(Error::expected(vec!["[Expression]"], Location::new(0, 0))),
            Some(t) => match t {
                Token::Identifier(loc, name) => Expression {
                    location: loc,
                    expression: ExpressionKind::Identifier(name),
                },
                Token::Integer(loc, value) => Expression {
                    location: loc,
                    expression: ExpressionKind::Integer(value),
                },
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
        let operator = self
            .parse_operator()
            .expect("there must be an operator as we got a precedence");
        let right = self.parse_expression(operator.precedence())?;
        Ok(Expression {
            location: left.location.clone(),
            expression: ExpressionKind::Binary(left.into(), operator, right.into()),
        })
    }

    fn parse_operator(&mut self) -> Option<Operator> {
        self.peek_token()
            .and_then(|t| t.try_into().ok())
            .map(|kind| Operator {
                location: self
                    .next_token()
                    .expect("there must be a next token, we were able to peek it")
                    .location()
                    .to_owned(),
                kind,
            })
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
