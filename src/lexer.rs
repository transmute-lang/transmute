use crate::error::Error;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Not;
use std::panic::panic_any;

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
        let bytes_read = match self.take_while(|c| c.is_whitespace()) {
            Ok((_, bytes_read)) => bytes_read,
            Err(_) => 0,
        };
        self.remaining = &self.remaining[bytes_read..];
        self.pos += bytes_read;

        let next = match self.remaining.chars().next() {
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
        let (kind, bytes_read) = match next {
            '+' => {
                self.location.column += 1;
                Ok((TokenKind::Plus, next.len_utf8()))
            }
            '*' => {
                self.location.column += 1;
                Ok((TokenKind::Star, next.len_utf8()))
            }
            '0'..='9' => Ok(self.number()?),
            c => Err(Error::UnexpectedChar(
                c,
                self.location.clone(),
                Span::new(self.pos, c.len_utf8()),
            )),
        }?;

        let token = Token {
            kind,
            location,
            span: Span::new(self.pos, bytes_read),
        };

        self.remaining = &self.remaining[bytes_read..];
        self.pos += bytes_read;

        Ok(token)
    }

    fn number(&mut self) -> Result<(TokenKind, usize), Error> {
        let (number, bytes_read) = self.take_while(|c| c.is_ascii_digit() || c == '_')?;

        let mut parsed = 0i64;
        for ch in number.chars() {
            parsed *= 10;
            if ch == '_' {
                continue;
            }

            parsed += (ch as u32 - '0' as u32) as i64;
        }

        Ok((TokenKind::Number(parsed), bytes_read))
    }

    fn take_while<F>(&mut self, pred: F) -> Result<(&str, usize), Error>
    where
        F: Fn(char) -> bool,
    {
        let mut end = 0;

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

            end += ch.len_utf8();
        }

        if end == 0 {
            Err(Error::NoMatch)
        } else {
            Ok((&self.remaining[..end], end))
        }
    }
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
    Number(i64),
    Plus,
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
                assert_eq!(expected, actual)
            }
        };
    }

    lexer_test_next!(next_number, "42" => 42; loc: 1,1; span: 0,2);
    lexer_test_next!(next_plus, "+" => TokenKind::Plus; loc: 1,1; span: 0,1);
    lexer_test_next!(next_star, "*" => TokenKind::Star; loc: 1,1; span: 0,1);

    macro_rules! lexer_test_fn {
        ($name:ident, $f:ident, $src:expr => $expected:expr) => {
            #[test]
            pub fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = TokenKind::from($expected);
                let (actual, _) = lexer.$f().unwrap();
                assert_eq!(expected, actual)
            }
        };
    }

    lexer_test_fn!(number, number, "42" => 42);

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
