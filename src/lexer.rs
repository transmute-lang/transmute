use crate::error::Error;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::str::Chars;

#[derive(Debug)]
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
                    span: Span::new(self.location.line, self.location.column, self.pos, 0),
                })
            }
        }?;

        let span = Span::new(
            self.location.line,
            self.location.column,
            self.pos,
            next.len_utf8(),
        );
        let (kind, span) = match next {
            '+' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::Plus, span))
            }
            '-' => match chars.next().unwrap_or_default() {
                '0'..='9' => Ok(self.number()?), // todo is that really useful?
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    Ok((TokenKind::Minus, span))
                }
            },
            '*' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::Star, span))
            }
            '/' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::Slash, span))
            }
            '=' => match chars.next().unwrap_or_default() {
                '=' => {
                    self.advance_columns(2);
                    let span = span.extend('='.len_utf8());
                    self.advance_consumed(span.len);
                    Ok((TokenKind::EqualEqual, span))
                }
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    Ok((TokenKind::Equal, span))
                }
            },
            '(' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::OpenParenthesis, span))
            }
            ')' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::CloseParenthesis, span))
            }
            ',' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::Comma, span))
            }
            '{' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::OpenCurlyBracket, span))
            }
            '}' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::CloseCurlyBracket, span))
            }
            ';' => {
                self.advance_column();
                self.advance_consumed(span.len);
                Ok((TokenKind::Semicolon, span))
            }
            c if c.is_ascii_digit() => Ok(self.number()?),
            c if c.is_ascii_alphabetic() || c == '_' => Ok(self.identifier()?),
            c => Err(Error::UnexpectedChar(c, span)),
        }?;

        Ok(Token { kind, span })
    }

    fn advance_column(&mut self) {
        self.advance_columns(1);
    }

    fn advance_columns(&mut self, count: usize) {
        self.location.column += count;
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
                let span = Span::new(
                    self.location.line,
                    self.location.column,
                    self.pos,
                    '-'.len_utf8(),
                );
                self.advance_consumed(span.len);

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
        fn make_keyword(
            lexer: &mut Lexer,
            chars: Chars,
            suffix: &str,
            token_kind: TokenKind,
            cols: usize,
            span: Span,
        ) -> Option<(TokenKind, Span)> {
            let mut span = span;
            let mut cols = cols;

            let mut suffix_chars = suffix.chars();

            for input_char in chars {
                if let Some(suffix_char) = suffix_chars.next() {
                    if suffix_char != input_char {
                        return None;
                    }
                    cols += 1;
                    span = span.extend(input_char.len_utf8());
                } else if is_identifier(&input_char) {
                    return None;
                } else {
                    break;
                }
            }

            lexer.advance_columns(cols);
            Some((token_kind, span))
        }

        let span = Span::new(self.location.line, self.location.column, self.pos, 0);
        let mut chars = self.remaining.chars();
        let keyword = match chars.next().expect("there is at least one char") {
            'f' => make_keyword(
                self,
                chars,
                "alse",
                TokenKind::False,
                1,
                span.extend('f'.len_utf8()),
            ),
            'l' => make_keyword(
                self,
                chars,
                "et",
                TokenKind::Let,
                1,
                span.extend('l'.len_utf8()),
            ),
            'r' => make_keyword(
                self,
                chars,
                "et",
                TokenKind::Ret,
                1,
                span.extend('r'.len_utf8()),
            ),
            't' => make_keyword(
                self,
                chars,
                "rue",
                TokenKind::True,
                1,
                span.extend('t'.len_utf8()),
            ),
            _ => None,
        };

        let (token, span) = match keyword {
            Some(keyword) => keyword,
            None => {
                let (ident, ident_span) = self.take_while(|c| is_identifier(&c))?;
                (TokenKind::Identifier(ident.to_string()), ident_span)
            }
        };

        self.advance_consumed(span.len);

        Ok((token, span))
    }

    fn take_while<F>(&mut self, pred: F) -> Result<(&str, Span), Error>
    where
        F: Fn(char) -> bool,
    {
        let line = self.location.line;
        let column = self.location.column;
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
            Ok((
                &self.remaining[..len],
                Span::new(line, column, self.pos, len),
            ))
        }
    }
}

fn is_identifier(c: &char) -> bool {
    c.is_ascii_alphanumeric() || c == &'_'
}

#[derive(Debug)]
pub struct PeekableLexer<'a> {
    lexer: Lexer<'a>,
    lookahead: usize,
    peeked: VecDeque<Result<Token, Error>>,
}

impl<'a> PeekableLexer<'a> {
    pub fn new(lexer: Lexer<'a>, lookahead: usize) -> Self {
        assert!(lookahead >= 1);
        Self {
            lexer,
            lookahead,
            peeked: VecDeque::with_capacity(lookahead),
        }
    }

    pub fn next(&mut self) -> Result<Token, Error> {
        self.peeked.pop_front().unwrap_or_else(|| self.lexer.next())
    }

    pub fn peek(&mut self) -> Result<&Token, &Error> {
        self.peek_nth(0)
    }

    pub fn peek_nth(&mut self, n: usize) -> Result<&Token, &Error> {
        assert!(n <= self.lookahead);
        if self.peeked.len() > n {
            return self
                .peeked
                .get(n)
                .expect("we just check, it's here")
                .as_ref();
        }

        while self.peeked.len() < n + 1 {
            self.peeked.push_back(self.lexer.next());
        }
        assert_eq!(self.peeked.len(), n + 1);

        self.peeked.back().expect("we just pushed it").as_ref()
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TokenKind {
    CloseCurlyBracket,
    CloseParenthesis,
    Comma,
    Equal,
    EqualEqual,
    False,
    Identifier(String),
    Let,
    Minus,
    Number(i64),
    OpenCurlyBracket,
    OpenParenthesis,
    Plus,
    Ret,
    Semicolon,
    Slash,
    Star,
    True,
    Eof,
}

impl From<i64> for TokenKind {
    fn from(value: i64) -> Self {
        Self::Number(value)
    }
}

#[derive(Clone, PartialEq)]
struct Location {
    /// 1-based line
    line: usize,
    /// 1-based column on line
    column: usize,
}

impl Location {
    fn new(line: usize, column: usize) -> Self {
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
    line: usize,
    column: usize,
    start: usize,
    len: usize,
}

impl Span {
    pub fn new(line: usize, column: usize, start: usize, len: usize) -> Self {
        assert!(line >= 1);
        assert!(column >= 1);
        Self {
            line,
            column,
            start,
            len,
        }
    }

    pub fn extend_to(&self, other: &Span) -> Self {
        let self_end = self.start + self.len;
        let other_end = other.start + other.len;
        let diff = other_end - self_end;
        Self {
            line: self.line,
            column: self.column,
            start: self.start,
            len: self.len + diff,
        }
    }

    pub fn extend(&self, len: usize) -> Self {
        Self {
            line: self.line,
            column: self.column,
            start: self.start,
            len: self.len + len,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}; [{}, {}]",
            self.line,
            self.column,
            self.start,
            self.start + self.len
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! lexer_test_next {
        ($name:ident, $src:expr => $expected:expr; loc: $line:expr,$column:expr; span: $start:expr,$len:expr) => {
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = Token {
                    kind: TokenKind::from($expected),
                    span: Span::new($line, $column, $start, $len),
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
    lexer_test_next!(next_equal_equal, "==" => TokenKind::EqualEqual; loc: 1,1; span: 0,2);
    lexer_test_next!(next_open_parenthesis, "(" => TokenKind::OpenParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(next_close_parenthesis, ")" => TokenKind::CloseParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(next_comma, "," => TokenKind::Comma; loc: 1,1; span: 0,1);
    lexer_test_next!(next_open_curly_bracket, "{" => TokenKind::OpenCurlyBracket; loc: 1,1; span: 0,1);
    lexer_test_next!(next_close_curly_bracket, "}" => TokenKind::CloseCurlyBracket; loc: 1,1; span: 0,1);
    lexer_test_next!(semicolon, ";" => TokenKind::Semicolon; loc: 1,1; span: 0,1);

    #[test]
    fn next_identifier() {
        let mut lexer = Lexer::new("ident");
        let expected = Token {
            kind: TokenKind::Identifier("ident".to_string()),
            span: Span::new(1, 1, 0, 5),
        };
        let actual = lexer.next().unwrap();
        assert_eq!(actual, expected);

        let mut lexer = Lexer::new(" ident ");
        let expected = Token {
            kind: TokenKind::Identifier("ident".to_string()),
            span: Span::new(1, 2, 1, 5),
        };
        let actual = lexer.next().unwrap();
        assert_eq!(actual, expected);
    }

    #[test]
    fn next_identifier_with_keyword_prefix() {
        let mut lexer = Lexer::new("let123");
        let expected = Token {
            kind: TokenKind::Identifier("let123".to_string()),
            span: Span::new(1, 1, 0, 6),
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
                    span: Span::new(1, 1, 0, $src.len()),
                };
                let actual = lexer.next().unwrap();
                assert_eq!(actual, expected);
            }
        };
    }

    lexer_test_keyword!(keyword_let, "let" => Let);
    lexer_test_keyword!(keyword_ret, "ret" => Ret);
    lexer_test_keyword!(keyword_true, "true" => True);
    lexer_test_keyword!(keyword_false, "false" => False);

    macro_rules! lexer_test_fn {
        ($name:ident, $f:ident, $src:expr => $expected:expr) => {
            #[test]
            fn $name() {
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
    fn peek_next_peek_next() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2"), 1);

        let token = lexer.peek().expect("a token ref");
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.peek().expect("a token ref");
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(2),
                span: Span::new(1, 3, 2, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(2),
                span: Span::new(1, 3, 2, 1),
            }
        );
    }

    #[test]
    fn peek_peek_next_next() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2"), 1);

        let token = lexer.peek().expect("a token ref");
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.peek().expect("a token ref");
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(2),
                span: Span::new(1, 3, 2, 1),
            }
        );
    }

    #[test]
    fn peek_nth() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 1);
        let span1 = lexer.peek().unwrap().span().clone();
        let span2 = lexer.peek_nth(0).unwrap().span().clone();
        assert_eq!(span1, span2);

        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 2);
        let span1 = lexer.peek_nth(2).unwrap().span().clone();
        let span2 = lexer.peek_nth(2).unwrap().span().clone();
        assert_eq!(span1, span2);
    }

    #[test]
    fn peek_nth_next() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 2);
        let _ = lexer.peek_nth(2).expect("token exists");

        let token = lexer.next().expect("a token");
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );
    }

    #[test]
    fn span_let_let() {
        let mut lexer = PeekableLexer::new(Lexer::new("let let"), 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 5);
    }

    #[test]
    fn span_ident_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("ident ident"), 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 7);
    }

    #[test]
    fn span_let_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("let ident"), 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 5);
    }

    #[test]
    fn span_ident_let() {
        let mut lexer = PeekableLexer::new(Lexer::new("ident let"), 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 7);
    }

    #[test]
    fn span_ident_with_keyword_prefix_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("let123 let"), 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 1);
        let token = lexer.next().expect("token exists");
        assert_eq!(token.span.column, 8);
    }
}
