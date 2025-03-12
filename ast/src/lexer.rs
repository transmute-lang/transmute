use std::borrow::Cow;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::fmt::{Debug, Display, Formatter};
use std::str::Chars;
use transmute_core::error::{Diagnostic, Diagnostics, Level};
use transmute_core::span::Span;

// fixme comments dont move spans (they behave as if the do not exist at all)

#[derive(Debug)]
pub struct Lexer<'s> {
    source: &'s str,
    remaining: &'s str,
    pos: usize,
    location: Location,
    diagnostics: Diagnostics,
}

impl<'s> Lexer<'s> {
    pub fn new(source: &'s str) -> Self {
        Self {
            source,
            remaining: source,
            pos: 0,
            location: Location::new(1, 1),
            diagnostics: Default::default(),
        }
    }

    fn skip_whitespaces_and_comments(&mut self) {
        loop {
            let mut read = false;
            if let Some(span) = self.take_while(|c| c.is_whitespace()) {
                self.advance_consumed(span.len);
                read = true;
            }
            if let Some('#') = self.remaining.chars().next() {
                self.advance_consumed(1);
                if let Some(span) = self.take_while(|c| c != '\n') {
                    self.advance_consumed(span.len + 1);
                }
                read = true;
            }
            if !read {
                break;
            }
        }
    }

    #[allow(clippy::should_implement_trait)] // todo:refactor maybe rename to next_token()?
    pub fn next(&mut self) -> Token {
        self.skip_whitespaces_and_comments();

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
                '0'..='9' => self.number(), // todo:question is that really useful?
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
                _ => todo!("issue a NOT here"),
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
            '[' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::OpenBracket, span)
            }
            ']' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::CloseBracket, span)
            }
            '.' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Dot, span)
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
            ':' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Colon, span)
            }
            ';' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::Semicolon, span)
            }
            '@' => {
                self.advance_column();
                self.advance_consumed(span.len);
                (TokenKind::At, span)
            }
            '"' => self.string(),
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

    fn string(&mut self) -> (TokenKind, Span) {
        let mut span = Span::new(self.location.line, self.location.column, self.pos, 1);
        let mut string = String::new();

        let mut chars = self.remaining[1..].chars();
        let mut escaped = false;
        loop {
            match chars.next() {
                None => {
                    self.diagnostics.push(Diagnostic::new(
                        "Missing \"",
                        Span::new(
                            self.location.line,
                            self.location.column,
                            self.pos + span.len,
                            0,
                        ),
                        Level::Error,
                        (file!(), line!()),
                    ));

                    self.advance_consumed(span.len);

                    return (TokenKind::String(string), span);
                }
                Some(ch) => {
                    if ch == '\n' {
                        self.location.line += 1;
                        self.location.column = 1;
                    } else {
                        self.location.column += 1;
                    }

                    span = span.extend(ch.len_utf8());
                    match ch {
                        '"' | '\\' if escaped => {
                            escaped = false;
                            string.push(ch);
                        }
                        'n' if escaped => {
                            escaped = false;
                            string.push('\n');
                        }
                        '\\' => escaped = true,
                        ch if escaped => {
                            escaped = false;
                            self.diagnostics.push(Diagnostic::new(
                                format!("Invalid escape char: {ch}"),
                                Span::new(
                                    self.location.line,
                                    self.location.column,
                                    self.pos + span.len,
                                    1,
                                ),
                                Level::Error,
                                (file!(), line!()),
                            ));
                            string.push(ch);
                        }
                        '"' => break,
                        ch => {
                            string.push(ch);
                        }
                    }
                }
            }
        }

        self.advance_consumed(span.len);

        (TokenKind::String(string), span)
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
        for ch in self.remaining[..digits_span.len].chars() {
            parsed *= 10;
            if ch == '_' {
                continue;
            }

            parsed += (ch as u32 - '0' as u32) as i64;
        }
        if negative {
            parsed = -parsed;
        }

        self.advance_consumed(digits_span.len);

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
            span: Span,
        ) -> Option<(TokenKind, Span)> {
            if chars.as_str().is_empty() {
                return None;
            }

            let mut span = span;
            let mut cols = 1;

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
            'a' => make_keyword(
                self,
                chars,
                "nnotation",
                TokenKind::Annotation,
                span.extend('a'.len_utf8()),
            ),
            'e' => make_keyword(
                self,
                chars,
                "lse",
                TokenKind::Else,
                span.extend('e'.len_utf8()),
            ),
            'f' => make_keyword(
                self,
                chars,
                "alse",
                TokenKind::False,
                span.extend('f'.len_utf8()),
            ),
            'i' => make_keyword(self, chars, "f", TokenKind::If, span.extend('f'.len_utf8())),
            'l' => make_keyword(
                self,
                chars,
                "et",
                TokenKind::Let,
                span.extend('l'.len_utf8()),
            ),
            'r' => make_keyword(
                self,
                chars,
                "et",
                TokenKind::Ret,
                span.extend('r'.len_utf8()),
            ),
            's' => make_keyword(
                self,
                chars,
                "truct",
                TokenKind::Struct,
                span.extend('t'.len_utf8()),
            ),
            't' => make_keyword(
                self,
                chars,
                "rue",
                TokenKind::True,
                span.extend('t'.len_utf8()),
            ),
            'w' => make_keyword(
                self,
                chars,
                "hile",
                TokenKind::While,
                span.extend('w'.len_utf8()),
            ),
            _ => None,
        };

        let (token, span) = match keyword {
            Some(keyword) => keyword,
            None => {
                let ident_span = self
                    .take_while(|c| is_identifier(&c))
                    .expect("there is only one identifier char");
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
            Some(Span::new(line, column, self.pos, len))
        }
    }

    pub fn span(&self, span: &Span) -> &str {
        &self.source[span.start..span.end()]
    }

    pub fn diagnostics(self) -> Diagnostics {
        self.diagnostics
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

    #[allow(clippy::should_implement_trait)] // todo:refactor maybe rename to next_token()?
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

    pub fn diagnostics(self) -> Diagnostics {
        self.lexer.diagnostics()
    }
}

#[derive(Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Token {
        Self { kind, span }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TokenKind {
    Annotation,
    At,
    CloseBracket,
    CloseCurlyBracket,
    CloseParenthesis,
    Colon,
    Comma,
    Dot,
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
    String(String),
    OpenBracket,
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
    Struct,
    Bad(String),
    Eof,
}

impl TokenKind {
    pub fn description(&self) -> Cow<'_, str> {
        match self {
            TokenKind::Annotation => Cow::from("`annotation`"),
            TokenKind::At => Cow::from("`@`"),
            TokenKind::CloseBracket => Cow::from("`]`"),
            TokenKind::CloseCurlyBracket => Cow::from("`}`"),
            TokenKind::CloseParenthesis => Cow::from("`)`"),
            TokenKind::Colon => Cow::from("`:`"),
            TokenKind::Comma => Cow::from("`,`"),
            TokenKind::Dot => Cow::from("`.`"),
            TokenKind::Else => Cow::from("`else`"),
            TokenKind::Equal => Cow::from("`=`"),
            TokenKind::EqualEqual => Cow::from("`==`"),
            TokenKind::ExclaimEqual => Cow::from("`!=`"),
            TokenKind::False => Cow::from("`false`"),
            TokenKind::Greater => Cow::from("`>`"),
            TokenKind::GreaterEqual => Cow::from("`>=`"),
            TokenKind::Identifier => Cow::from("identifier"),
            TokenKind::If => Cow::from("`if`"),
            TokenKind::Let => Cow::from("`let`"),
            TokenKind::Minus => Cow::from("`-`"),
            TokenKind::Number(_) => Cow::from("number"),
            TokenKind::String(_) => Cow::from("string"),
            TokenKind::OpenBracket => Cow::from("`[`"),
            TokenKind::OpenCurlyBracket => Cow::from("`{`"),
            TokenKind::OpenParenthesis => Cow::from("`(`"),
            TokenKind::Plus => Cow::from("`+`"),
            TokenKind::Ret => Cow::from("`ret`"),
            TokenKind::Semicolon => Cow::from("`;`"),
            TokenKind::Slash => Cow::from("`/`"),
            TokenKind::Smaller => Cow::from("`<`"),
            TokenKind::SmallerEqual => Cow::from("`<=`"),
            TokenKind::Star => Cow::from("`*`"),
            TokenKind::True => Cow::from("`true`"),
            TokenKind::While => Cow::from("`while`"),
            TokenKind::Bad(s) => Cow::from(format!("`{s}`")),
            TokenKind::Eof => Cow::from("`eof`"),
            TokenKind::Struct => Cow::from("`struct`"),
        }
    }

    fn discriminant(&self) -> u8 {
        match self {
            TokenKind::Identifier => 0,
            TokenKind::Number(_) => 1,
            TokenKind::String(_) => 2,
            TokenKind::True => 3,
            TokenKind::False => 4,

            TokenKind::Let => 5,
            TokenKind::Ret => 6,
            TokenKind::If => 7,
            TokenKind::Else => 8,
            TokenKind::While => 9,
            TokenKind::Struct => 10,
            TokenKind::Annotation => 11,

            TokenKind::Comma => 12,
            TokenKind::Semicolon => 13,
            TokenKind::Colon => 14,
            TokenKind::Dot => 15,

            TokenKind::CloseCurlyBracket => 16,
            TokenKind::CloseParenthesis => 17,
            TokenKind::OpenCurlyBracket => 18,
            TokenKind::OpenParenthesis => 19,

            TokenKind::Equal => 20,

            TokenKind::Star => 21,
            TokenKind::Slash => 22,

            TokenKind::Minus => 23,
            TokenKind::Plus => 24,

            TokenKind::EqualEqual => 25,
            TokenKind::ExclaimEqual => 26,
            TokenKind::Greater => 27,
            TokenKind::GreaterEqual => 28,
            TokenKind::Smaller => 29,
            TokenKind::SmallerEqual => 30,

            TokenKind::CloseBracket => 31,
            TokenKind::OpenBracket => 32,

            TokenKind::At => 33,

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
            TokenKind::Annotation => {
                write!(f, "`annotation`")
            }
            TokenKind::At => {
                write!(f, "`@`")
            }
            TokenKind::CloseBracket => {
                write!(f, "`]`")
            }
            TokenKind::CloseCurlyBracket => {
                write!(f, "`}}`")
            }
            TokenKind::CloseParenthesis => {
                write!(f, "`)`")
            }
            TokenKind::Colon => {
                write!(f, "`:`")
            }
            TokenKind::Comma => {
                write!(f, "`,`")
            }
            TokenKind::Dot => {
                write!(f, "`.`")
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
            TokenKind::Number(n) => {
                write!(f, "number({n})")
            }
            TokenKind::String(s) => {
                write!(f, "string({s})")
            }
            TokenKind::OpenBracket => {
                write!(f, "`[`")
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
            TokenKind::Bad(s) => {
                write!(f, "`{s}`")
            }
            TokenKind::Eof => {
                write!(f, "`eof`")
            }
            TokenKind::Struct => {
                write!(f, "`struct`")
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

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_debug_snapshot;

    macro_rules! lexer_test_next {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($src);
                let actual = lexer.next();

                assert!(lexer.diagnostics.is_empty());
                assert_debug_snapshot!(actual);
            }
        };

        ($name:ident, $src:expr, $diagnostic:expr) => {
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($src);
                let actual = lexer.next();

                assert!(!lexer.diagnostics.is_empty());
                assert_eq!(
                    lexer.diagnostics.iter().next().unwrap().message,
                    $diagnostic
                );
                assert_debug_snapshot!(actual);
            }
        };
    }

    lexer_test_next!(next_number, "42");
    lexer_test_next!(next_neg_number, "-42");
    lexer_test_next!(next_number_suffix, "42a");
    lexer_test_next!(next_string, "\"hello\"");
    lexer_test_next!(next_string_empty, "\"\"");
    lexer_test_next!(next_string_with_double_quotes, "\"\\\"hello\\\"\"");
    lexer_test_next!(next_string_with_backslash, "\" \\\\ \"");
    lexer_test_next!(next_string_newline_escaped, "\"line1\\nline2\"");
    lexer_test_next!(next_string_newline, "\"line1\nline2\"");
    lexer_test_next!(
        next_string_invalid_escape,
        "\"\\g\"",
        "Invalid escape char: g"
    );
    lexer_test_next!(next_string_not_closed, "\"hello", "Missing \"");
    lexer_test_next!(next_plus, "+");
    lexer_test_next!(next_minus, "-");
    lexer_test_next!(next_star, "*");
    lexer_test_next!(next_slash, "/");
    lexer_test_next!(next_equal, "=");
    lexer_test_next!(next_equal_equal, "==");
    lexer_test_next!(next_exclam_equal, "!=");
    lexer_test_next!(next_greater, ">");
    lexer_test_next!(next_smller, "<");
    lexer_test_next!(next_greater_equal, ">=");
    lexer_test_next!(next_smaller_equal, "<=");
    lexer_test_next!(next_open_parenthesis, "(");
    lexer_test_next!(next_close_parenthesis, ")");
    lexer_test_next!(next_comma, ",");
    lexer_test_next!(next_dot, ".");
    lexer_test_next!(next_open_curly_bracket, "{");
    lexer_test_next!(next_close_curly_bracket, "}");
    lexer_test_next!(next_open_bracket, "[");
    lexer_test_next!(next_close_bracket, "]");
    lexer_test_next!(semicolon, ";");
    lexer_test_next!(colon, ":");
    lexer_test_next!(at, "@");
    lexer_test_next!(bad, "\\");
    lexer_test_next!(comment, "#!transmute\n+");
    lexer_test_next!(eof, "");
    lexer_test_next!(identifier, "ident");
    lexer_test_next!(identifier_space, " ident ");
    lexer_test_next!(identifier_with_keyword_prefix, "let123");
    lexer_test_next!(keyword_let, "let");
    lexer_test_next!(keyword_ret, "ret");
    lexer_test_next!(keyword_if, "if");
    lexer_test_next!(keyword_else, "else");
    lexer_test_next!(keyword_while, "while");
    lexer_test_next!(keyword_true, "true");
    lexer_test_next!(keyword_false, "false");
    lexer_test_next!(keyword_struct, "struct");
    lexer_test_next!(keyword_annotation, "annotation");
    lexer_test_next!(keyword_a, "a");

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
        let span1 = lexer.peek().span.clone();
        let span2 = lexer.peek_nth(0).span.clone();
        assert_eq!(span1, span2);

        let mut lexer = PeekableLexer::new(Lexer::new("1 2 3 4"), 2);
        let span1 = lexer.peek_nth(2).span.clone();
        let span2 = lexer.peek_nth(2).span.clone();
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
