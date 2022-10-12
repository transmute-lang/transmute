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
}

impl TryFrom<&Token> for BinaryOperatorKind {
    type Error = ();

    fn try_from(token: &Token) -> std::result::Result<Self, Self::Error> {
        use BinaryOperatorKind::*;
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
            .map(|k: BinaryOperatorKind| k.precedence())
    }

    fn parse_expression(&mut self, precedence: OperatorPrecedence) -> Result<Expression> {
        // todo see if we can refactor this
        let mut expression = match self.next_token() {
            // fixme proper location
            None => return Err(Error::expected(vec!["[expression]"], Location::new(0, 0))),
            Some(t) => match t {
                Token::LeftParenthesis(loc) => todo!(),
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
                t => {
                    return Err(Error::expected_but_got(
                        vec!["!", "-", "identifier", "integer"],
                        &t,
                    ))
                }
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

    fn parse_unary_expression(&mut self, operator: UnaryOperator) -> Result<Expression> {
        Ok(Expression {
            location: operator.location.clone(),
            expression: ExpressionKind::Unary(
                operator,
                self.parse_expression(OperatorPrecedence::Prefix)?.into(),
            ),
        })
    }

    /// parses `[(] ( [expression] [,] )* [expression]? [)]`
    fn parse_call_expression(
        &mut self,
        method_name_location: Location,
        method_name: String,
    ) -> Result<Expression> {
        // todo better location
        let parenthesis_location = match self.next_token() {
            None => return Err(Error::expected(vec!["("], method_name_location)),
            Some(Token::LeftParenthesis(parenthesis_location)) => parenthesis_location,
            Some(token) => return Err(Error::expected_but_got(vec!["("], &token)),
        };

        let mut parameters = Vec::new();
        while let Some(token) = self.peek_token() {
            match token {
                Token::RightParenthesis(_) => break,
                Token::Comma(_) if !parameters.is_empty() => {
                    self.next_token()
                        .expect("we are sure there is one as we just peeked it");
                    if let Some(Token::RightParenthesis(_)) = self.peek_token() {
                        break;
                    }
                }
                _ => {
                    // todo add ")" in the list of accepted chars in the returned error
                    parameters.push(self.parse_expression(OperatorPrecedence::Lowest)?);
                }
            }
        }

        match self.next_token() {
            // todo better location
            None => return Err(Error::expected(vec![")"], method_name_location)),
            Some(Token::RightParenthesis(_)) => (),
            Some(token) => return Err(Error::expected_but_got(vec![")"], &token)),
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
        let right = self.parse_expression(operator.precedence())?;
        Ok(Expression {
            location: left.location.clone(),
            expression: ExpressionKind::Binary(left.into(), operator, right.into()),
        })
    }

    fn parse_operator(&mut self) -> Option<BinaryOperator> {
        self.peek_token()
            .and_then(|t| t.try_into().ok())
            .map(|kind| BinaryOperator {
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
                let node = parser.parse_expression(OperatorPrecedence::Lowest);
                let next_node = parser.parse_expression(OperatorPrecedence::Lowest);
                let node: Expression = node.unwrap();

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
    }
}
