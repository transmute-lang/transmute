use crate::error::Error;
use std::fmt::{Display, Formatter};

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
        let next = match self.remaining.chars().next() {
            Some(c) => Ok(c),
            None => Err(Error::UnexpectedEof),
        }?;

        let location = self.location.clone();
        let (token, bytes_read) = match next {
            '0'..='9' => Ok(self.number()?),
            c => Err(Error::UnexpectedChar(
                c,
                self.location.clone(),
                Span::new(self.pos, c.len_utf8()),
            )),
        }?;

        let token = Token::new(token, location, Span::new(self.pos, bytes_read));

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

#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub location: Location,
    pub span: Span,
}

impl Token {
    fn new(kind: TokenKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    Number(i64),
}

impl From<i64> for TokenKind {
    fn from(value: i64) -> Self {
        Self::Number(value)
    }
}

#[derive(Debug, Clone, PartialEq)]
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

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Span {
    /// start position
    start: usize,
    /// length
    len: usize,
}

impl Span {
    pub fn new(start: usize, len: usize) -> Self {
        Self { start, len }
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
                let expected = Token::new(
                    TokenKind::from($expected),
                    Location::new($l, $c),
                    Span::new($start, $len),
                );
                let actual = lexer.next().unwrap();
                assert_eq!(expected, actual)
            }
        };
    }

    lexer_test_next!(next_number, "42" => 42; loc: 1,1; span: 0,2);

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
}
