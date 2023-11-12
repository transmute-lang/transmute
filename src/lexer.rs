use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::str::Chars;

#[derive(Debug)]
pub struct Lexer<'s> {
    source: &'s str,
    remaining: &'s str,
    pos: usize,
    location: Location,
}

impl<'s> Lexer<'s> {
    pub fn new(source: &'s str) -> Self {
        Self {
            source,
            remaining: source,
            pos: 0,
            location: Location::new(1, 1),
        }
    }

    pub fn next(&mut self) -> Token {
        if let Some(span) = self.take_while(|c| c.is_whitespace()) {
            self.advance_consumed(span.len());
        }

        let mut chars = self.remaining.chars();
        let next = match chars.next() {
            Some(c) => c,
            None => {
                return Token {
                    kind: TokenKind::Eof,
                    span: Span::new(self.location.line, self.location.column, self.pos, 0),
                }
            }
        };

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
                (TokenKind::Plus, span)
            }
            '-' => match chars.next().unwrap_or_default() {
                '0'..='9' => self.number(), // todo is that really useful?
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    (TokenKind::Minus, span)
                }
            },
            '*' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Star, span)
            }
            '/' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Slash, span)
            }
            '=' => match chars.next().unwrap_or_default() {
                '=' => {
                    self.advance_columns(2);
                    let span = span.extend('='.len_utf8());
                    self.advance_consumed(span.len);
                    (TokenKind::EqualEqual, span)
                }
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    (TokenKind::Equal, span)
                }
            },
            '!' => match chars.next().unwrap_or_default() {
                '=' => {
                    self.advance_columns(2);
                    let span = span.extend('='.len_utf8());
                    self.advance_consumed(span.len);
                    (TokenKind::ExclaimEqual, span)
                }
                _ => todo!(),
            },
            '>' => match chars.next().unwrap_or_default() {
                '=' => {
                    self.advance_columns(2);
                    let span = span.extend('='.len_utf8());
                    self.advance_consumed(span.len);
                    (TokenKind::GreaterEqual, span)
                }
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    (TokenKind::Greater, span)
                }
            },
            '<' => match chars.next().unwrap_or_default() {
                '=' => {
                    self.advance_columns(2);
                    let span = span.extend('='.len_utf8());
                    self.advance_consumed(span.len);
                    (TokenKind::SmallerEqual, span)
                }
                _ => {
                    self.advance_column();
                    self.advance_consumed(span.len);
                    (TokenKind::Smaller, span)
                }
            },
            '(' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::OpenParenthesis, span)
            }
            ')' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::CloseParenthesis, span)
            }
            ',' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Comma, span)
            }
            '{' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::OpenCurlyBracket, span)
            }
            '}' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::CloseCurlyBracket, span)
            }
            ';' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Semicolon, span)
            }
            c if c.is_ascii_digit() => self.number(),
            c if c.is_ascii_alphabetic() || c == '_' => self.identifier(),
            c => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Bad(c.to_string()), span)
            }
        };

        Token { kind, span }
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

    fn number(&mut self) -> (TokenKind, Span) {
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

        let digits_span = self
            .take_while(|c| c.is_ascii_digit() || c == '_')
            .expect("we have at least one digit");

        let mut parsed = 0i64;
        for ch in self.remaining[..digits_span.len()].chars() {
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

        (
            TokenKind::Number(parsed),
            span.map(|s| s.extend_to(&digits_span))
                .unwrap_or(digits_span),
        )
    }

    fn identifier(&mut self) -> (TokenKind, Span) {
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
        let keyword = match chars.next().expect("there is at least one ident char") {
            'e' => make_keyword(
                self,
                chars,
                "lse",
                TokenKind::Else,
                1,
                span.extend('e'.len_utf8()),
            ),
            'f' => make_keyword(
                self,
                chars,
                "alse",
                TokenKind::False,
                1,
                span.extend('f'.len_utf8()),
            ),
            'i' => make_keyword(
                self,
                chars,
                "f",
                TokenKind::If,
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
            'w' => make_keyword(
                self,
                chars,
                "hile",
                TokenKind::While,
                1,
                span.extend('w'.len_utf8()),
            ),
            _ => None,
        };

        let (token, span) = match keyword {
            Some(keyword) => keyword,
            None => {
                let ident_span = self
                    .take_while(|c| is_identifier(&c))
                    .expect("there is ony one identifier char");
                (TokenKind::Identifier, ident_span)
            }
        };

        self.advance_consumed(span.len);

        (token, span)
    }

    fn take_while<F>(&mut self, pred: F) -> Option<Span>
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
            None
        } else {
            Some(
                //(
                // &self.remaining[..len],
                Span::new(line, column, self.pos, len),
            ) //)
        }
    }

    pub fn span(&self, span: &Span) -> &str {
        &self.source[span.start..span.end()]
    }
}

fn is_identifier(c: &char) -> bool {
    c.is_ascii_alphanumeric() || c == &'_'
}

#[derive(Debug)]
pub struct PeekableLexer<'s> {
    lexer: Lexer<'s>,
    lookahead: usize,
    peeked: VecDeque<Token>,
}

impl<'s> PeekableLexer<'s> {
    pub fn new(lexer: Lexer<'s>, lookahead: usize) -> Self {
        assert!(lookahead >= 1);
        Self {
            lexer,
            lookahead,
            peeked: VecDeque::with_capacity(lookahead),
        }
    }

    pub fn next(&mut self) -> Token {
        self.peeked.pop_front().unwrap_or_else(|| self.lexer.next())
    }

    pub fn push_next(&mut self, token: Token) {
        self.peeked.push_front(token);
    }

    pub fn peek(&mut self) -> &Token {
        self.peek_nth(0)
    }

    pub fn peek_nth(&mut self, n: usize) -> &Token {
        assert!(n <= self.lookahead);
        if self.peeked.len() > n {
            return self.peeked.get(n).expect("we just check, it's here");
        }

        while self.peeked.len() < n + 1 {
            self.peeked.push_back(self.lexer.next());
        }
        assert_eq!(self.peeked.len(), n + 1);

        self.peeked.back().expect("we just pushed it")
    }

    pub fn span(&self, span: &Span) -> &str {
        self.lexer.span(span)
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    kind: TokenKind,
    span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Token {
        Self { kind, span }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    CloseCurlyBracket,
    CloseParenthesis,
    Comma,
    Else,
    Equal,
    EqualEqual,
    ExclaimEqual,
    False,
    Greater,
    GreaterEqual,
    Identifier,
    If,
    Let,
    Minus,
    Number(i64),
    OpenCurlyBracket,
    OpenParenthesis,
    Plus,
    Ret,
    Semicolon,
    Slash,
    Smaller,
    SmallerEqual,
    Star,
    True,
    While,
    Bad(String),
    Eof,
}

impl TokenKind {
    fn discriminant(&self) -> u8 {
        match self {
            TokenKind::Identifier => 0,
            TokenKind::Number(_) => 1,
            TokenKind::True => 2,
            TokenKind::False => 3,

            TokenKind::Let => 4,
            TokenKind::Ret => 5,
            TokenKind::If => 6,
            TokenKind::Else => 7,
            TokenKind::While => 8,

            TokenKind::Comma => 9,
            TokenKind::Semicolon => 10,

            TokenKind::CloseCurlyBracket => 11,
            TokenKind::CloseParenthesis => 12,
            TokenKind::OpenCurlyBracket => 13,
            TokenKind::OpenParenthesis => 14,

            TokenKind::Equal => 15,

            TokenKind::Star => 16,
            TokenKind::Slash => 17,

            TokenKind::Minus => 18,
            TokenKind::Plus => 19,

            TokenKind::EqualEqual => 20,
            TokenKind::ExclaimEqual => 21,
            TokenKind::Greater => 22,
            TokenKind::GreaterEqual => 23,
            TokenKind::Smaller => 24,
            TokenKind::SmallerEqual => 25,

            TokenKind::Eof => 254,
            TokenKind::Bad(_) => 255,
        }
    }
}

impl PartialOrd for TokenKind {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.discriminant().cmp(&other.discriminant()))
    }
}

impl Ord for TokenKind {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenKind::CloseCurlyBracket => {
                write!(f, "`}}`")
            }
            TokenKind::CloseParenthesis => {
                write!(f, "`)`")
            }
            TokenKind::Comma => {
                write!(f, "`,`")
            }
            TokenKind::Else => {
                write!(f, "`else`")
            }
            TokenKind::Equal => {
                write!(f, "`=`")
            }
            TokenKind::EqualEqual => {
                write!(f, "`==`")
            }
            TokenKind::ExclaimEqual => {
                write!(f, "`!=`")
            }
            TokenKind::False => {
                write!(f, "`false`")
            }
            TokenKind::Greater => {
                write!(f, "`>`")
            }
            TokenKind::GreaterEqual => {
                write!(f, "`>=`")
            }
            TokenKind::Identifier => {
                write!(f, "identifier")
            }
            TokenKind::If => {
                write!(f, "`if`")
            }
            TokenKind::Let => {
                write!(f, "`let`")
            }
            TokenKind::Minus => {
                write!(f, "`-`")
            }
            TokenKind::Number(_) => {
                write!(f, "number") // todo implement description instead
            }
            TokenKind::OpenCurlyBracket => {
                write!(f, "`{{`")
            }
            TokenKind::OpenParenthesis => {
                write!(f, "`(`")
            }
            TokenKind::Plus => {
                write!(f, "`+`")
            }
            TokenKind::Ret => {
                write!(f, "`ret`")
            }
            TokenKind::Semicolon => {
                write!(f, "`;`")
            }
            TokenKind::Slash => {
                write!(f, "`/`")
            }
            TokenKind::Smaller => {
                write!(f, "`<`")
            }
            TokenKind::SmallerEqual => {
                write!(f, "`<=`")
            }
            TokenKind::Star => {
                write!(f, "`*`")
            }
            TokenKind::True => {
                write!(f, "`true`")
            }
            TokenKind::While => {
                write!(f, "`while`")
            }
            TokenKind::Bad(c) => {
                write!(f, "`{}`", c)
            }
            TokenKind::Eof => {
                write!(f, "`eof`")
            }
        }
    }
}

impl From<i64> for TokenKind {
    fn from(value: i64) -> Self {
        Self::Number(value)
    }
}

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

#[derive(Clone, Eq)]
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

    pub fn line(&self) -> usize {
        self.line
    }

    pub fn column(&self) -> usize {
        self.column
    }

    pub fn start(&self) -> usize {
        self.start
    }

    fn end(&self) -> usize {
        self.start + self.len
    }
}

impl PartialEq<Self> for Span {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.len == other.len
    }
}

impl PartialOrd<Self> for Span {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        if self.start < other.start {
            return Ordering::Less;
        }
        if self.start == other.start && self.len < other.len {
            return Ordering::Less;
        }
        Ordering::Greater
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
                let actual = lexer.next();
                assert_eq!(actual, expected)
            }
        };
    }

    lexer_test_next!(next_number, "42" => 42; loc: 1,1; span: 0,2);
    lexer_test_next!(next_neg_number, "-42" => -42; loc: 1,1; span: 0,3);
    lexer_test_next!(next_number_suffix, "42a" => 42; loc: 1,1; span: 0,2);
    lexer_test_next!(next_plus, "+" => TokenKind::Plus; loc: 1,1; span: 0,1);
    lexer_test_next!(next_minus, "-" => TokenKind::Minus; loc: 1,1; span: 0,1);
    lexer_test_next!(next_star, "*" => TokenKind::Star; loc: 1,1; span: 0,1);
    lexer_test_next!(next_slash, "/" => TokenKind::Slash; loc: 1,1; span: 0,1);
    lexer_test_next!(next_equal, "=" => TokenKind::Equal; loc: 1,1; span: 0,1);
    lexer_test_next!(next_equal_equal, "==" => TokenKind::EqualEqual; loc: 1,1; span: 0,2);
    lexer_test_next!(next_exclam_equal, "!=" => TokenKind::ExclaimEqual; loc: 1,1; span: 0,2);
    lexer_test_next!(next_greater, ">" => TokenKind::Greater; loc: 1,1; span: 0,1);
    lexer_test_next!(next_smller, "<" => TokenKind::Smaller; loc: 1,1; span: 0,1);
    lexer_test_next!(next_greater_equal, ">=" => TokenKind::GreaterEqual; loc: 1,1; span: 0,2);
    lexer_test_next!(next_smaller_equal, "<=" => TokenKind::SmallerEqual; loc: 1,1; span: 0,2);
    lexer_test_next!(next_open_parenthesis, "(" => TokenKind::OpenParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(next_close_parenthesis, ")" => TokenKind::CloseParenthesis; loc: 1,1; span: 0,1);
    lexer_test_next!(next_comma, "," => TokenKind::Comma; loc: 1,1; span: 0,1);
    lexer_test_next!(next_open_curly_bracket, "{" => TokenKind::OpenCurlyBracket; loc: 1,1; span: 0,1);
    lexer_test_next!(next_close_curly_bracket, "}" => TokenKind::CloseCurlyBracket; loc: 1,1; span: 0,1);
    lexer_test_next!(semicolon, ";" => TokenKind::Semicolon; loc: 1,1; span: 0,1);
    lexer_test_next!(bad, "\\" => TokenKind::Bad("\\".to_string()); loc: 1,1; span: 0,1);
    lexer_test_next!(eof, "" => TokenKind::Eof; loc: 1,1; span: 0,0);

    #[test]
    fn eof_after_tokens() {
        let mut lexer = Lexer::new("1");
        // consume 1
        lexer.next();

        for x in 0..2 {
            let eof = lexer.next();
            assert_eq!(
                eof,
                Token {
                    kind: TokenKind::Eof,
                    span: Span::new(1, 2, 1, 0),
                },
                "next() nr {} failed",
                x
            );
        }
    }

    #[test]
    fn next_identifier() {
        let mut lexer = Lexer::new("ident");
        let expected = Token {
            kind: TokenKind::Identifier,
            span: Span::new(1, 1, 0, 5),
        };
        let actual = lexer.next();
        assert_eq!(actual, expected);

        let mut lexer = Lexer::new(" ident ");
        let expected = Token {
            kind: TokenKind::Identifier,
            span: Span::new(1, 2, 1, 5),
        };
        let actual = lexer.next();
        assert_eq!(actual, expected);
    }

    #[test]
    fn next_identifier_with_keyword_prefix() {
        let mut lexer = Lexer::new("let123");
        let expected = Token {
            kind: TokenKind::Identifier,
            span: Span::new(1, 1, 0, 6),
        };
        let actual = lexer.next();
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
                let actual = lexer.next();
                assert_eq!(actual, expected);
            }
        };
    }

    lexer_test_keyword!(keyword_let, "let" => Let);
    lexer_test_keyword!(keyword_ret, "ret" => Ret);
    lexer_test_keyword!(keyword_if, "if" => If);
    lexer_test_keyword!(keyword_else, "else" => Else);
    lexer_test_keyword!(keyword_while, "while" => While);
    lexer_test_keyword!(keyword_true, "true" => True);
    lexer_test_keyword!(keyword_false, "false" => False);

    macro_rules! lexer_test_fn {
        ($name:ident, $f:ident, $src:expr => $expected:expr) => {
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($src);
                let expected = TokenKind::from($expected);
                let (actual, _) = lexer.$f();
                assert_eq!(actual, expected)
            }
        };
    }

    lexer_test_fn!(number, number, "42" => 42);
    lexer_test_fn!(neg_number, number, "-42" => -42);

    #[test]
    fn peek_next_peek_next() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2"), 1);

        let token = lexer.peek();
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next();
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.peek();
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(2),
                span: Span::new(1, 3, 2, 1),
            }
        );

        let token = lexer.next();
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

        let token = lexer.peek();
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.peek();
        assert_eq!(
            token,
            &Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next();
        assert_eq!(
            token,
            Token {
                kind: TokenKind::Number(1),
                span: Span::new(1, 1, 0, 1),
            }
        );

        let token = lexer.next();
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
        let span1 = lexer.peek().span().clone();
        let span2 = lexer.peek_nth(0).span().clone();
        assert_eq!(span1, span2);

        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 2);
        let span1 = lexer.peek_nth(2).span().clone();
        let span2 = lexer.peek_nth(2).span().clone();
        assert_eq!(span1, span2);
    }

    #[test]
    fn peek_nth_next() {
        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 2);
        let _ = lexer.peek_nth(2);

        let token = lexer.next();
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
        let token = lexer.next();
        assert_eq!(token.span.column, 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 5);
    }

    #[test]
    fn span_ident_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("ident ident"), 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 7);
    }

    #[test]
    fn span_let_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("let ident"), 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 5);
    }

    #[test]
    fn span_ident_let() {
        let mut lexer = PeekableLexer::new(Lexer::new("ident let"), 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 7);
    }

    #[test]
    fn span_ident_with_keyword_prefix_ident() {
        let mut lexer = PeekableLexer::new(Lexer::new("let123 let"), 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 1);
        let token = lexer.next();
        assert_eq!(token.span.column, 8);
    }
}
