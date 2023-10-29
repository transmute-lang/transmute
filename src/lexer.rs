use crate::error::Error;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};

pub struct Lexer<'a> {
    remaining: &'a str,
    pos: usize,
    location: Location,
}

impl<'a> Lexer<'a> {
    pub fn new(source: &'a str) -> Self {
        Self {
            remaining: source,
            pos: 0,
            location: Location::new(1, 1),
        }
    }

    pub fn next(&mut self) -> Result<Token, Error> {
        if let Ok((_, span)) = self.take_while(|c| c.is_whitespace()) {
            self.advance_consumed(span.len());
        }

        let mut chars = self.remaining.chars();
        let next = match chars.next() {
            Some(c) => Ok(c),
            None => {
                return Ok(Token {
                    kind: TokenKind::Eof,
                    location: self.location.clone(),
                    span: Span::new(self.pos, 0),
                })
            }
        }?;

        let location = self.location.clone();
        let span = Span::new(self.pos, next.len_utf8());
        let (kind, span) = match next {
            '+' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::Plus, span))
            }
            '-' => match chars.next().unwrap_or_default() {
                '0'..='9' => Ok(self.number()?), // todo is that really useful?
                _ => {
                    self.advance_column();
                    self.advance_span(&span);
                    Ok((TokenKind::Minus, span))
                }
            },
            '*' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::Star, span))
            }
            '/' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::Slash, span))
            }
            '=' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::Equal, span))
            }
            '(' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::OpenParenthesis, span))
            }
            ')' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::CloseParenthesis, span))
            }
            ';' => {
                self.advance_column();
                self.advance_span(&span);
                Ok((TokenKind::Semicolon, span))
            }
            c if c.is_ascii_digit() => Ok(self.number()?),
            c if c.is_ascii_alphabetic() || c == '_' => Ok(self.identifier()?),
            c => Err(Error::UnexpectedChar(
                c,
                self.location.clone(),
                Span::new(self.pos, c.len_utf8()),
            )),
        }?;

        let token = Token {
            kind,
            location,
            span,
        };

        Ok(token)
    }

    fn advance_column(&mut self) {
        self.location.column += 1;
    }

    fn advance_span(&mut self, span: &Span) {
        self.advance_consumed(span.len())
    }

    fn advance_consumed(&mut self, len: usize) {
        self.remaining = &self.remaining[len..];
        self.pos += len;
    }

    fn number(&mut self) -> Result<(TokenKind, Span), Error> {
        let (negative, span) = match self
            .remaining
            .chars()
            .next()
            .expect("we have at least one char")
        {
            '-' => {
                let span = Span::new(self.pos, '-'.len_utf8());
                self.advance_span(&span);

                (true, Some(span))
            }
            _ => (false, None),
        };

        let (number, digits_span) = self.take_while(|c| c.is_ascii_digit() || c == '_')?;

        let mut parsed = 0i64;
        for ch in number.chars() {
            parsed *= 10;
            if ch == '_' {
                continue;
            }

            parsed += (ch as u32 - '0' as u32) as i64;
        }
        if negative {
            parsed = -parsed;
        }

        self.advance_consumed(digits_span.len());

        Ok((
            TokenKind::Number(parsed),
            span.map(|s| s.extend_to(&digits_span))
                .unwrap_or(digits_span),
        ))
    }

    fn identifier(&mut self) -> Result<(TokenKind, Span), Error> {
        let mut chars = self.remaining.chars().peekable();

        let mut bytes_read = 0usize;
        let keyword_token = match chars.next().expect("there is at least one char") {
            'l' => {
                self.advance_column();
                bytes_read += 'l'.len_utf8();
                match chars.next() {
                    Some('e') => {
                        self.advance_column();
                        bytes_read += 'e'.len_utf8();
                        match chars.next() {
                            Some('t') => match chars.peek() {
                                Some(c) if is_identifier(c) => None,
                                _ => {
                                    self.advance_column();
                                    bytes_read += 't'.len_utf8();
                                    Some(TokenKind::Let)
                                }
                            },
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };

        let (token, span) = match keyword_token {
            Some(token) => (token, Span::new(self.pos, bytes_read)),
            None => {
                let (_, span) = self.take_while(|c| is_identifier(&c))?;
                let bytes_read = bytes_read + span.len();
                (
                    TokenKind::Identifier(self.remaining[..bytes_read].to_string()),
                    Span::new(self.pos, bytes_read),
                )
            }
        };

        self.advance_span(&span);

        Ok((token, span))
    }

    fn take_while<F>(&mut self, pred: F) -> Result<(&str, Span), Error>
    where
        F: Fn(char) -> bool,
    {
        let mut len = 0;

        for ch in self.remaining.chars() {
            if !pred(ch) {
                break;
            }

            if ch == '\n' {
                self.location.line += 1;
                self.location.column = 1;
            } else {
                self.location.column += 1;
            }

            len += ch.len_utf8();
        }

        if len == 0 {
            Err(Error::NoMatch)
        } else {
            Ok((&self.remaining[..len], Span::new(self.pos, len)))
        }
    }
}

fn is_identifier(c: &char) -> bool {
    c.is_ascii_alphanumeric() || c == &'_'
}

pub struct PeekableLexer<'a> {
    lexer: Lexer<'a>,
    peeked: VecDeque<Result<Token, Error>>,
}

impl<'a> PeekableLexer<'a> {
    pub fn new(lexer: Lexer<'a>, lookahead: usize) -> Self {
        assert!(lookahead >= 1);
        Self {
            lexer,
            peeked: VecDeque::with_capacity(lookahead),
        }
    }

    pub fn next(&mut self) -> Result<Token, Error> {
        self.peeked.pop_front().unwrap_or_else(|| self.lexer.next())
    }

    pub fn peek(&mut self) -> &Result<Token, Error> {
        if self.peeked.is_empty() {
            self.peeked.push_back(self.lexer.next())
        }
        self.peeked.front().expect("we just pushed one")
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    kind: TokenKind,
    location: Location,
    span: Span,
}

impl Token {
    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn location(&self) -> &Location {
        &self.location
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    CloseParenthesis,
    Equal,
    Identifier(String),
    Let,
    Minus,
    Number(i64),
    OpenParenthesis,
    Plus,
    Semicolon,
    Slash,
    Star,
    Eof,
}

impl From<i64> for TokenKind {
    fn from(value: i64) -> Self {
        Self::Number(value)
    }
}

#[derive(Clone, PartialEq)]
pub struct Location {
    /// 1-based line
    line: usize,
    /// 1-based column on line
    column: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Self {
        Self { line, column }
    }
}

impl Debug for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

#[derive(Clone, PartialEq)]
pub struct Span {
    /// start position
    start: usize,
    /// length
    end: usize,
}

impl Span {
    pub fn new(start: usize, len: usize) -> Self {
        Self {
            start,
            end: start + len - 1,
        }
    }

    pub fn start(&self) -> usize {
        self.start
    }

    pub fn end(&self) -> usize {
        self.end
    }

    pub fn extend_to(&self, other: &Span) -> Self {
        Self {
            start: self.start,
            end: other.end,
        }
    }

    pub fn len(&self) -> usize {
        self.end - self.start + 1
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}->{}", self.start, self.end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! lexer_test_next {
        ($name:ident, $src:expr => $expected:expr; loc: $l:expr,$c:expr; span: $start:expr,$len:expr) => {
            #[test]
            pub fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = Token {
                    kind: TokenKind::from($expected),
                    location: Location::new($l, $c),
                    span: Span::new($start, $len),
                };
                let actual = lexer.next().unwrap();
                assert_eq!(actual, expected)
            }
        };
    }

    lexer_test_next!(next_number, "42" => 42; loc: 1,1; span: 0,2);
    lexer_test_next!(next_neg_number, "-42" => -42; loc: 1,1; span: 0,3);
    lexer_test_next!(next_plus, "+" => TokenKind::Plus; loc: 1,1; span: 0,1);
    lexer_test_next!(next_minus, "-" => TokenKind::Minus; loc: 1,1; span: 0,1);
    lexer_test_next!(next_star, "*" => TokenKind::Star; loc: 1,1; span: 0,1);
    lexer_test_next!(next_slash, "/" => TokenKind::Slash; loc: 1,1; span: 0,1);
    lexer_test_next!(next_equal, "=" => TokenKind::Equal; loc: 1,1; span: 0,1);
    lexer_test_next!(next_open_parenthesis, "(" => TokenKind::OpenParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(next_close_parenthesis, ")" => TokenKind::CloseParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(semicolon, ";" => TokenKind::Semicolon; loc: 1,1; span: 0,1);

    #[test]
    fn next_identifier() {
        let mut lexer = Lexer::new("ident");
        let expected = Token {
            kind: TokenKind::Identifier("ident".to_string()),
            location: Location::new(1, 1),
            span: Span::new(0, 5),
        };
        let actual = lexer.next().unwrap();
        assert_eq!(actual, expected);

        let mut lexer = Lexer::new(" ident ");
        let expected = Token {
            kind: TokenKind::Identifier("ident".to_string()),
            location: Location::new(1, 2),
            span: Span::new(1, 5),
        };
        let actual = lexer.next().unwrap();
        assert_eq!(actual, expected);
    }

    fn next_identifier_with_keyword_prefix() {
        let mut lexer = Lexer::new("let123");
        let expected = Token {
            kind: TokenKind::Identifier("let123".to_string()),
            location: Location::new(1, 1),
            span: Span::new(0, 6),
        };
        let actual = lexer.next().unwrap();
        assert_eq!(actual, expected);
    }

    macro_rules! lexer_test_keyword {
        ($name:ident, $src:expr => $keyword:ident) => {
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = Token {
                    kind: TokenKind::$keyword,
                    location: Location::new(1, 1),
                    span: Span::new(0, $src.len()),
                };
                let actual = lexer.next().unwrap();
                assert_eq!(actual, expected);
            }
        };
    }

    lexer_test_keyword!(keyword_let, "let" => Let);

    macro_rules! lexer_test_fn {
        ($name:ident, $f:ident, $src:expr => $expected:expr) => {
            #[test]
            pub fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = TokenKind::from($expected);
                let (actual, _) = lexer.$f().unwrap();
                assert_eq!(actual, expected)
            }
        };
    }

    lexer_test_fn!(number, number, "42" => 42);
    lexer_test_fn!(neg_number, number, "-42" => -42);

    #[test]
    fn peek() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2"), 1);

        let token = lexer.peek().as_ref().expect("a token ref");
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                location: Location::new(1, 1),
                span: Span::new(0, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                location: Location::new(1, 1),
                span: Span::new(0, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(2),
                location: Location::new(1, 3),
                span: Span::new(2, 1),
            }
        );
    }
}
