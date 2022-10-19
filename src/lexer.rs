use std::fmt::{Debug, Display, Formatter};
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Location {
    line: usize,
    column: usize,
}

impl Location {
    pub fn new(line: usize, column: usize) -> Location {
        Self { line, column }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

pub struct Token {
    pub location: Location,
    pub kind: TokenKind,
    pub value: TokenValue,
}

impl Token {
    pub fn value_string(self) -> Option<String> {
        if let TokenValue::String(string) = self.value {
            Some(string)
        } else {
            None
        }
    }
}

impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use TokenKind::*;
        match &self.kind {
            And => write!(f, "[and]"),
            Comma => write!(f, "[,]"),
            Continue => write!(f, "[continue]"),
            Dot => write!(f, "[.]"),
            Eof => write!(f, "[EOF]"),
            Equal => write!(f, "[=]"),
            EqualEqual => write!(f, "[==]"),
            EqualGt => write!(f, "[=>]"),
            Exclam => write!(f, "[!]"),
            ExclamEqual => write!(f, "[!=]"),
            ExclamTilde => write!(f, "[!~]"),
            Fail => write!(f, "[fail]"),
            Fn => write!(f, "[fn]"),
            Fork => write!(f, "[fork]"),
            Gt => write!(f, "[>]"),
            GtEqual => write!(f, "[>=]"),
            Identifier => write!(f, "[identifier:{:?}]", self.value),
            Integer => write!(f, "[integer:{:?}]", self.value),
            Invalid => write!(f, "[invalid:{:?}]", self.value),
            Join => write!(f, "[join]"),
            LeftBrace => write!(f, "[{{]"),
            LeftBracket => write!(f, "[[]"),
            LeftParenthesis => write!(f, "[(]"),
            Let => write!(f, "[let]"),
            Lt => write!(f, "[<]"),
            LtEqual => write!(f, "[<=]"),
            Match => write!(f, "[match]"),
            Minus => write!(f, "[-]"),
            Null => write!(f, "[null]"),
            Or => write!(f, "[or]"),
            Percent => write!(f, "[%]"),
            Pipe => write!(f, "[|]"),
            Plus => write!(f, "[+]"),
            RightBrace => write!(f, "[}}]"),
            RightBracket => write!(f, "[]]"),
            RightParenthesis => write!(f, "[)]"),
            Semicolon => write!(f, "[;]"),
            Slash => write!(f, "[/]"),
            Star => write!(f, "[*]"),
            String => write!(f, "[string:{:?}]", self.value),
            Tilde => write!(f, "[~]"),
            Underscore => write!(f, "[_]"),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use TokenKind::*;
        match &self.kind {
            Identifier => write!(f, "{}", self.value),
            Integer => write!(f, "{}", self.value),
            Invalid => match &self.value {
                TokenValue::Error(ErrorKind::UnterminatedString) => {
                    write!(f, "UNTERMINATED_STRING")
                }
                TokenValue::Error(ErrorKind::Unexpected(c)) => write!(f, "_{}_", c),
                // todo find better representati)on
                TokenValue::Error(ErrorKind::ExpectedAny) => write!(f, "ANY"),
                // todo find better representation
                TokenValue::Error(ErrorKind::ExpectedOneOf(v)) => write!(f, "({})", v.join(", ")),
                _ => unreachable!(),
            },
            String => write!(f, "\"{}\"", self.value),
            _ => write!(f, "{}", self.kind),
        }
    }
}

#[derive(Debug)]
pub enum TokenKind {
    And,
    Comma,
    Continue,
    Dot,
    Eof,
    Equal,
    EqualEqual,
    EqualGt,
    Exclam,
    ExclamEqual,
    ExclamTilde,
    Fail,
    Fn,
    Fork,
    Gt,
    GtEqual,
    Identifier,
    Integer,
    Invalid,
    Join,
    LeftBrace,
    LeftBracket,
    LeftParenthesis,
    Let,
    Lt,
    LtEqual,
    Match,
    Minus,
    Null,
    Or,
    Percent,
    Pipe,
    Plus,
    RightBrace,
    RightBracket,
    RightParenthesis,
    Semicolon,
    Slash,
    Star,
    String,
    Tilde,
    Underscore,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use TokenKind::*;
        match &self {
            And => write!(f, "and"),
            Comma => write!(f, ","),
            Continue => write!(f, "continue"),
            Dot => write!(f, "."),
            Eof => write!(f, "EOF"),
            Equal => write!(f, "="),
            EqualEqual => write!(f, "=="),
            EqualGt => write!(f, "=>"),
            Exclam => write!(f, "!"),
            ExclamEqual => write!(f, "!="),
            ExclamTilde => write!(f, "!~"),
            Fail => write!(f, "fail"),
            Fn => write!(f, "fn"),
            Fork => write!(f, "fork"),
            Gt => write!(f, ">"),
            GtEqual => write!(f, ">="),
            Identifier => write!(f, "IDENTIFIER"),
            Integer => write!(f, "INTEGER"),
            Invalid => write!(f, "INVALID"),
            Join => write!(f, "join"),
            LeftBrace => write!(f, "{{"),
            LeftBracket => write!(f, ""),
            LeftParenthesis => write!(f, "("),
            Let => write!(f, "let"),
            Lt => write!(f, "<"),
            LtEqual => write!(f, "<="),
            Match => write!(f, "match"),
            Minus => write!(f, "-"),
            Null => write!(f, "null"),
            Or => write!(f, "or"),
            Percent => write!(f, "%"),
            Pipe => write!(f, "|"),
            Plus => write!(f, "+"),
            RightBrace => write!(f, "}}"),
            RightBracket => write!(f, ""),
            RightParenthesis => write!(f, ")"),
            Semicolon => write!(f, ";"),
            Slash => write!(f, "/"),
            Star => write!(f, "*"),
            String => write!(f, "STRING"),
            Tilde => write!(f, "~"),
            Underscore => write!(f, "_"),
        }
    }
}

#[derive(Debug)]
pub enum TokenValue {
    None,
    String(String),
    Integer(u32),
    Error(ErrorKind),
}

impl Display for TokenValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use TokenValue::*;
        match self {
            None => Ok(()),
            String(s) => write!(f, "{}", s),
            Integer(i) => write!(f, "{}", i),
            Error(e) => write!(f, "{:?}", e),
        }
    }
}

#[derive(Debug)]
pub enum ErrorKind {
    ExpectedOneOf(Vec<String>),
    ExpectedAny,
    Unexpected(char),
    UnterminatedString,
}

pub struct Lexer<'t> {
    source: &'t str,
    iter: Peekable<Chars<'t>>,
    curr_char: Option<char>,
    location: Location,
    eof: bool,
}

impl<'t> Lexer<'t> {
    pub fn new(source: &'t str) -> Self {
        Self {
            source,
            iter: source.chars().peekable(),
            curr_char: None,
            location: Location::new(1, 0),
            eof: false,
        }
    }

    /// Reads and return the next char; returns `None` when there is none.
    fn next_char(&mut self) -> Option<char> {
        self.curr_char = self.iter.next();
        match self.curr_char {
            Some('\n') => {
                self.location.column = 0;
                self.location.line += 1;
                Some('\n')
            }
            Some(c) => {
                self.location.column += 1;
                Some(c)
            }
            _ => None,
        }
    }

    fn peek_char(&mut self) -> Option<char> {
        self.iter.peek().map(|c| c.to_owned())
    }

    fn skip_whitespaces_and_comments(&mut self) {
        while let Some(c) = self.next_char() {
            match c {
                '#' => self.skip_line_comment(),
                '/' => match self.peek_char() {
                    Some('/') => self.skip_line_comment(),
                    Some('*') => {
                        self.next_char();
                        self.skip_multiline_comment()
                    }
                    _ => break,
                },
                c if c.is_whitespace() => continue,
                _ => break,
            }
        }
    }

    fn skip_line_comment(&mut self) {
        while let Some(c) = self.next_char() {
            if c == '\n' {
                break;
            }
        }
    }

    fn skip_multiline_comment(&mut self) {
        while let Some(c) = self.next_char() {
            match c {
                '*' => {
                    if let Some('/') = self.next_char() {
                        break;
                    }
                }
                _ => continue,
            }
        }
    }

    /// Creates a string token, using `\` as escape character.
    fn make_string(&mut self, location: Location) -> Token {
        let mut string = String::new();

        loop {
            match self.next_char() {
                None => {
                    return Token {
                        location,
                        kind: TokenKind::Invalid,
                        value: TokenValue::Error(ErrorKind::UnterminatedString),
                    };
                }
                Some('"') => {
                    return Token {
                        location,
                        kind: TokenKind::String,
                        value: TokenValue::String(string),
                    }
                }
                Some('\\') => match self.next_char() {
                    None => {
                        return Token {
                            location: Location {
                                line: self.location.line,
                                column: self.location.column + 1,
                            },
                            kind: TokenKind::Invalid,
                            value: TokenValue::Error(ErrorKind::ExpectedOneOf(vec![
                                "\"".to_string(),
                                "\\".to_string(),
                            ])),
                        };
                    }
                    Some(c) => string.push(c),
                },
                Some(c) => string.push(c),
            }
        }
    }

    /// Creates a block string. Block string start with `"""`, followed by a single char delimiter
    /// and optionally a `\n`. It end at the first occurrence of the delimiter. Whitespaces on the
    /// beginning of the first line are dropped and the same amount of whitespaces is dropped on
    /// each subsequent line as well. Note that the delimiter is dropped as well.
    ///
    /// Example:
    /// ```text
    /// sql = """;
    ///     select * from table
    ///     where column = 'value';
    /// ```
    /// becomes:
    /// ```text
    /// select * from table
    /// where column = 'value'
    /// ```
    fn make_block_string(&mut self, location: Location) -> Token {
        // todo if the delimiter is ";", don't eat it at the end
        let delimiter = self.next_char();
        if delimiter.is_none() {
            return Token {
                location,
                kind: TokenKind::Invalid,
                value: TokenValue::Error(ErrorKind::ExpectedAny),
            };
        }
        let delimiter = delimiter.unwrap();

        // eat the fist optional newline after the delimiter
        if let Some('\n') = self.peek_char() {
            self.next_char();
        }

        // here the string begins. we first drop and count the amount of whitespaces on the first
        // line appearing before the first non-whitespace char., so we can drop them on the
        // subsequent lines as well.
        let mut string = String::new();
        let mut prefix = 0;

        while let Some(c) = self.next_char() {
            match c {
                c if c == delimiter => {
                    return Token {
                        location,
                        kind: TokenKind::String,
                        value: TokenValue::String(string),
                    }
                }
                c if c.is_whitespace() && c != '\n' => prefix += 1,
                c => {
                    string.push(c);
                    break;
                }
            }
        }

        let prefix = prefix;
        let mut whitespaces_left = prefix;
        while let Some(c) = self.next_char() {
            match c {
                '\n' => {
                    string.push(c);
                    whitespaces_left = prefix;
                }
                c if c == delimiter => {
                    return Token {
                        location,
                        kind: TokenKind::String,
                        value: TokenValue::String(string),
                    }
                }
                c if c.is_whitespace() && whitespaces_left > 0 => whitespaces_left -= 1,
                c => {
                    string.push(c);
                    whitespaces_left = 0;
                }
            }
        }

        Token {
            location,
            kind: TokenKind::Invalid,
            value: TokenValue::Error(ErrorKind::UnterminatedString),
        }
    }

    /// Creates a 32 bits unsigned number token.
    fn make_number(&mut self, location: Location) -> Token {
        let mut number: u32 = self.curr_char.unwrap().to_digit(10).unwrap();
        while let Some(c) = self.peek_char() {
            if c.is_ascii_digit() {
                self.next_char();
                number *= 10;
                number += c.to_digit(10).unwrap();
            } else {
                break;
            }
        }
        Token {
            location,
            kind: TokenKind::Integer,
            value: TokenValue::Integer(number),
        }
    }

    /// Creates either a keyword token or an identifier one.
    fn make_identifier(&mut self, location: Location) -> Token {
        let mut string = String::from(self.curr_char.unwrap());

        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                self.next_char();
                string.push(c);
            } else {
                break;
            }
        }

        match string.as_str() {
            "and" => Token {
                location,
                kind: TokenKind::And,
                value: TokenValue::None,
            },
            "continue" => Token {
                location,
                kind: TokenKind::Continue,
                value: TokenValue::None,
            },
            "fail" => Token {
                location,
                kind: TokenKind::Fail,
                value: TokenValue::None,
            },
            "fn" => Token {
                location,
                kind: TokenKind::Fn,
                value: TokenValue::None,
            },
            "fork" => Token {
                location,
                kind: TokenKind::Fork,
                value: TokenValue::None,
            },
            "join" => Token {
                location,
                kind: TokenKind::Join,
                value: TokenValue::None,
            },
            "let" => Token {
                location,
                kind: TokenKind::Let,
                value: TokenValue::None,
            },
            "match" => Token {
                location,
                kind: TokenKind::Match,
                value: TokenValue::None,
            },
            "null" => Token {
                location,
                kind: TokenKind::Null,
                value: TokenValue::None,
            },
            "or" => Token {
                location,
                kind: TokenKind::Or,
                value: TokenValue::None,
            },
            _ => Token {
                location,
                kind: TokenKind::Identifier,
                value: TokenValue::String(string),
            },
        }
    }
}

/// Returns `next_char()` if `peek_char()` returns any of the provided chars.
/// ```
/// next_char_if!(self, 'a', 'b')
/// ```
/// is turned into
/// ```
/// match self.peek_char() {
///     Some('a') => self.next_char(),
///     Some('b') => self.next_char(),
///     _ => None,
/// }
/// ```
macro_rules! next_char_if {
    ($self:expr, $($expr:expr),*) => {{
        match $self.peek_char() {
            $(Some($expr) => $self.next_char(),)+
            _ => None,
        }
    }}
}

impl<'t> Iterator for Lexer<'t> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespaces_and_comments();

        let location = self.location.clone();

        let token = match self.curr_char {
            Some(';') => Token {
                location,
                kind: TokenKind::Semicolon,
                value: TokenValue::None,
            },
            Some(',') => Token {
                location,
                kind: TokenKind::Comma,
                value: TokenValue::None,
            },
            Some('_') => Token {
                location,
                kind: TokenKind::Underscore,
                value: TokenValue::None,
            },
            Some('|') => Token {
                location,
                kind: TokenKind::Pipe,
                value: TokenValue::None,
            },
            Some('.') => Token {
                location,
                kind: TokenKind::Dot,
                value: TokenValue::None,
            },
            Some('+') => Token {
                location,
                kind: TokenKind::Plus,
                value: TokenValue::None,
            },
            Some('-') => Token {
                location,
                kind: TokenKind::Minus,
                value: TokenValue::None,
            },
            Some('*') => Token {
                location,
                kind: TokenKind::Star,
                value: TokenValue::None,
            },
            Some('/') => Token {
                location,
                kind: TokenKind::Slash,
                value: TokenValue::None,
            },
            Some('%') => Token {
                location,
                kind: TokenKind::Percent,
                value: TokenValue::None,
            },
            Some('~') => Token {
                location,
                kind: TokenKind::Tilde,
                value: TokenValue::None,
            },
            Some('=') => match next_char_if!(self, '=', '>') {
                Some('=') => Token {
                    location,
                    kind: TokenKind::EqualEqual,
                    value: TokenValue::None,
                },
                Some('>') => Token {
                    location,
                    kind: TokenKind::EqualGt,
                    value: TokenValue::None,
                },
                _ => Token {
                    location,
                    kind: TokenKind::Equal,
                    value: TokenValue::None,
                },
            },
            Some('!') => match next_char_if!(self, '=', '~') {
                Some('=') => Token {
                    location,
                    kind: TokenKind::ExclamEqual,
                    value: TokenValue::None,
                },
                Some('~') => Token {
                    location,
                    kind: TokenKind::ExclamTilde,
                    value: TokenValue::None,
                },
                _ => Token {
                    location,
                    kind: TokenKind::Exclam,
                    value: TokenValue::None,
                },
            },
            Some('(') => Token {
                location,
                kind: TokenKind::LeftParenthesis,
                value: TokenValue::None,
            },
            Some(')') => Token {
                location,
                kind: TokenKind::RightParenthesis,
                value: TokenValue::None,
            },
            Some('{') => Token {
                location,
                kind: TokenKind::LeftBrace,
                value: TokenValue::None,
            },
            Some('}') => Token {
                location,
                kind: TokenKind::RightBrace,
                value: TokenValue::None,
            },
            Some('[') => Token {
                location,
                kind: TokenKind::LeftBracket,
                value: TokenValue::None,
            },
            Some(']') => Token {
                location,
                kind: TokenKind::RightBracket,
                value: TokenValue::None,
            },
            Some('>') => match next_char_if!(self, '=') {
                Some('=') => Token {
                    location,
                    kind: TokenKind::GtEqual,
                    value: TokenValue::None,
                },
                _ => Token {
                    location,
                    kind: TokenKind::Gt,
                    value: TokenValue::None,
                },
            },
            Some('<') => match next_char_if!(self, '=') {
                Some('=') => Token {
                    location,
                    kind: TokenKind::LtEqual,
                    value: TokenValue::None,
                },
                _ => Token {
                    location,
                    kind: TokenKind::Lt,
                    value: TokenValue::None,
                },
            },
            Some('"') => match next_char_if!(self, '"') {
                Some('"') => match next_char_if!(self, '"') {
                    Some('"') => self.make_block_string(location),
                    _ => Token {
                        location,
                        kind: TokenKind::String,
                        value: TokenValue::String("".to_string()),
                    },
                },
                _ => self.make_string(location),
            },
            Some(c) if c.is_ascii_digit() => self.make_number(location),
            Some(c) if c.is_alphabetic() => self.make_identifier(location),
            Some(c) => Token {
                location,
                kind: TokenKind::Invalid,
                value: TokenValue::Error(ErrorKind::Unexpected(c)),
            },
            None if !self.eof => {
                self.eof = true;
                return Some(Token {
                    location: Location {
                        line: location.line,
                        column: location.column + 1,
                    },
                    kind: TokenKind::Eof,
                    value: TokenValue::None,
                });
            }
            _ => return None,
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // todo test for unterminated strings

    #[test]
    fn eof_is_last_token() {
        let mut lexer = Lexer::new("");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::Eof,
                location: Location { line: 1, column: 1 },
                ..
            }
        ));

        let token = lexer.next();
        assert!(token.is_none());
    }

    #[test]
    fn skip_whitespaces() {
        let mut lexer = Lexer::new(" ");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::Eof,
                location: Location { line: 1, column: 2 },
                ..
            }
        ));
    }

    #[test]
    fn skip_c_line_comment() {
        let mut lexer = Lexer::new("// [\n]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::RightBracket,
                ..
            }
        ));
    }

    #[test]
    fn skip_shell_line_comment() {
        let mut lexer = Lexer::new("# [\n]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::RightBracket,
                ..
            }
        ));
    }

    #[test]
    fn skip_multiline_comment() {
        let mut lexer = Lexer::new("/*\n[ */ ]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::RightBracket,
                ..
            }
        ));
    }

    #[test]
    fn skip_empty_multiline_comment() {
        let mut lexer = Lexer::new("/**/]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                kind: TokenKind::RightBracket,
                ..
            }
        ));
    }

    #[test]
    fn unexpected() {
        let mut lexer = Lexer::new("§");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token {
                location: Location { line: 1, column: 1 },
                kind: TokenKind::Invalid,
                value: TokenValue::Error(ErrorKind::Unexpected('§'))
            },
        ));
    }

    macro_rules! empty_token {
        ($($name:ident: $str:expr => $token:pat,)*) => {
        $(
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($str);
                let token = lexer.next();
                let token = token.expect("token must be Some");
                assert!(matches!(token, $token), "got {:?}", token);
            }
        )*
        }
    }

    empty_token! {
        token_and:               "and"       => Token{ kind: TokenKind::And,..},
        token_comma:             ","         => Token{ kind: TokenKind::Comma,..},
        token_continue:          "continue"  => Token{ kind: TokenKind::Continue,..},
        token_dot:               "."         => Token{ kind: TokenKind::Dot,..},
        token_eof:               ""          => Token{ kind: TokenKind::Eof,..},
        token_equal:             "="         => Token{ kind: TokenKind::Equal,..},
        token_equal_equal:       "=="        => Token{ kind: TokenKind::EqualEqual,..},
        token_equal_gt:          "=>"        => Token{ kind: TokenKind::EqualGt,..},
        token_exclam:            "!"         => Token{ kind: TokenKind::Exclam,..},
        token_exclam_equal:      "!="        => Token{ kind: TokenKind::ExclamEqual,..},
        token_exclam_tilde:      "!~"        => Token{ kind: TokenKind::ExclamTilde,..},
        token_fail:              "fail"      => Token{ kind: TokenKind::Fail,..},
        token_fn:                "fn"        => Token{ kind: TokenKind::Fn,..},
        token_fork:              "fork"      => Token{ kind: TokenKind::Fork,..},
        token_gt:                ">"         => Token{ kind: TokenKind::Gt,..},
        token_gt_equal:          ">="        => Token{ kind: TokenKind::GtEqual,..},
        token_join:              "join"      => Token{ kind: TokenKind::Join,..},
        token_left_brace:        "{"         => Token{ kind: TokenKind::LeftBrace,..},
        token_left_bracket:      "["         => Token{ kind: TokenKind::LeftBracket,..},
        token_left_parenthesis:  "("         => Token{ kind: TokenKind::LeftParenthesis,..},
        token_let:               "let"       => Token{ kind: TokenKind::Let,..},
        token_lt:                "<"         => Token{ kind: TokenKind::Lt,..},
        token_lt_equal:          "<="        => Token{ kind: TokenKind::LtEqual,..},
        token_match:             "match"     => Token{ kind: TokenKind::Match,..},
        token_minus:             "-"         => Token{ kind: TokenKind::Minus,..},
        token_null:              "null"      => Token{ kind: TokenKind::Null,..},
        token_or:                "or"        => Token{ kind: TokenKind::Or,..},
        token_percent:           "%"         => Token{ kind: TokenKind::Percent,..},
        token_pipe:              "|"         => Token{ kind: TokenKind::Pipe,..},
        token_plus:              "+"         => Token{ kind: TokenKind::Plus,..},
        token_right_brace:       "}"         => Token{ kind: TokenKind::RightBrace,..},
        token_right_bracket:     "]"         => Token{ kind: TokenKind::RightBracket,..},
        token_right_parenthesis: ")"         => Token{ kind: TokenKind::RightParenthesis,..},
        token_semicolon:         ";"         => Token{ kind: TokenKind::Semicolon,..},
        token_slash:             "/"         => Token{ kind: TokenKind::Slash,..},
        token_star:              "*"         => Token{ kind: TokenKind::Star,..},
        token_tilde:             "~"         => Token{ kind: TokenKind::Tilde,..},
        token_underscore:        "_"         => Token{ kind: TokenKind::Underscore,..},
        token_loc_1_1:           "+"         => Token{ kind: TokenKind::Plus, location: Location{line:1,column:1},..},
        token_loc_2_1:           "\n+"       => Token{ kind: TokenKind::Plus, location: Location{line:2,column:1},..},
        token_loc_1_2:           " +"        => Token{ kind: TokenKind::Plus, location: Location{line:1,column:2},..},
        token_loc_2_2:           "\n +"      => Token{ kind: TokenKind::Plus, location: Location{line:2,column:2},..},
    }

    #[test]
    fn sequence_dot_equal() {
        let mut lexer = Lexer::new(".=");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Equal,
                ..
            })
        ));
    }

    #[test]
    fn sequence_empty_string_dot() {
        let mut lexer = Lexer::new("\"\".");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::String,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_string_dot() {
        let mut lexer = Lexer::new("\"str\".");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::String,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_block_string_dot() {
        let mut lexer = Lexer::new("\"\"\";\nline1;.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::String,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_identifier_dot() {
        let mut lexer = Lexer::new("identifier.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Identifier,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_integer_dot() {
        let mut lexer = Lexer::new("200.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Integer,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_exclam_dot() {
        let mut lexer = Lexer::new("!.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Exclam,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_equal_dot() {
        let mut lexer = Lexer::new("=.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Equal,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_gt_dot() {
        let mut lexer = Lexer::new(">.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Gt,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    #[test]
    fn sequence_lt_dot() {
        let mut lexer = Lexer::new("<.");
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Lt,
                ..
            })
        ));
        let token = lexer.next();
        assert!(matches!(
            token,
            Some(Token {
                kind: TokenKind::Dot,
                ..
            })
        ));
    }

    macro_rules! string {
        ($($name:ident: $strin:expr => $strout:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($strin);
                let token = lexer.next().expect("expected Some");
                assert!(if let Token{ kind: TokenKind::String, value: TokenValue::String( string), ..} = token {
                    assert_eq!(string, $strout);
                    true
                } else {
                    false
                });
            }
        )*
        }
    }

    string! {
        empty_string:           "\"\""                         => "",
        simple_string:          "\"string\""                   => "string",
        escaped_string:         "\"\\\"\""                     => "\"",
        multiline_string:       "\"\nline1\nline2;\""          => "\nline1\nline2;",
        multiline_block_string: "\"\"\";\n  line 1\n  line 2;" => "line 1\nline 2",
    }

    #[test]
    fn integer() {
        let mut lexer = Lexer::new("200");
        let token = lexer.next().expect("expected Some");
        assert!(if let Token {
            kind: TokenKind::Integer,
            value: TokenValue::Integer(integer),
            ..
        } = token
        {
            assert_eq!(integer, 200);
            true
        } else {
            false
        });
    }

    #[test]
    fn identifier() {
        let mut lexer = Lexer::new("identifier");
        let token = lexer.next().expect("expected Some");
        assert!(if let Token {
            kind: TokenKind::Identifier,
            value: TokenValue::String(identifier),
            ..
        } = token
        {
            assert_eq!(identifier, "identifier");
            true
        } else {
            false
        });
    }
}
