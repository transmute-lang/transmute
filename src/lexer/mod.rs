use std::fmt::{Display, Formatter};
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug)]
pub struct Error {
    error: String,
    location: Location,
}

impl Error {
    fn expected_but_got(expectations: Vec<&str>, received: &char, location: Location) -> Self {
        if received == &'\n' {
            Self::err(
                format!("expected `{}`, got `\\n`", expectations.join("` or `")),
                location,
            )
        } else {
            Self::err(
                format!(
                    "expected `{}`, got `{}`",
                    expectations.join("` or `"),
                    received
                ),
                location,
            )
        }
    }

    fn expected(expectations: Vec<&str>, location: Location) -> Self {
        Self::err(
            format!("expected `{}`, got nothing", expectations.join("` or `")),
            location,
        )
    }

    fn expected_any_char(location: Location) -> Self {
        Self::err("expected any character, got nothing".to_string(), location)
    }

    fn unexpected(received: &char, location: Location) -> Self {
        Self::err(format!("unexpected `{}`", received), location)
    }

    fn err(error: String, location: Location) -> Self {
        Self { error, location }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Lexing error: {} at {}", self.error, self.location)
    }
}

type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Location {
    line: usize,
    column: usize,
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

pub enum Token {
    Amp(Location),
    And(Location),
    Comma(Location),
    Continue(Location),
    Dot(Location),
    Equal(Location),
    EqualEqual(Location),
    EqualGt(Location),
    ExclamEqual(Location),
    ExclamTilde(Location),
    Fail(Location),
    Fn(Location),
    Fork(Location),
    Join(Location),
    Identifier(Location, String),
    Integer(Location, u32),
    LeftBrace(Location),
    LeftBracket(Location),
    Let(Location),
    Match(Location),
    Null(Location),
    Or(Location),
    Pipe(Location),
    RightBrace(Location),
    RightBracket(Location),
    Semicolon(Location),
    String(Location, String),
    Tilde(Location),
    Underscore(Location),
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Amp(_) => write!(f, "[&]"),
            Token::And(_) => write!(f, "[and]"),
            Token::Comma(_) => write!(f, "[,]"),
            Token::Continue(_) => write!(f, "[continue]"),
            Token::Dot(_) => write!(f, "[.]"),
            Token::Equal(_) => write!(f, "[=]"),
            Token::EqualEqual(_) => write!(f, "[==]"),
            Token::EqualGt(_) => write!(f, "[=>]"),
            Token::ExclamEqual(_) => write!(f, "[!=]"),
            Token::ExclamTilde(_) => write!(f, "[!~]"),
            Token::Fail(_) => write!(f, "[fail]"),
            Token::Fn(_) => write!(f, "[fn]"),
            Token::Fork(_) => write!(f, "[fork]"),
            Token::Join(_) => write!(f, "[join]"),
            Token::Identifier(_, value) => write!(f, "[identifier:{}]", value),
            Token::Integer(_, value) => write!(f, "[integer:{}]", value),
            Token::LeftBrace(_) => write!(f, "[{{]"),
            Token::LeftBracket(_) => write!(f, "[[]"),
            Token::Let(_) => write!(f, "[let]"),
            Token::Match(_) => write!(f, "[match]"),
            Token::Null(_) => write!(f, "[null]"),
            Token::Or(_) => write!(f, "[or]"),
            Token::Pipe(_) => write!(f, "[|]"),
            Token::RightBrace(_) => write!(f, "[}}]"),
            Token::RightBracket(_) => write!(f, "[]]"),
            Token::Semicolon(_) => write!(f, "[;]"),
            Token::String(_, value) => write!(f, "[string:{}]", value),
            Token::Tilde(_) => write!(f, "[~]"),
            Token::Underscore(_) => write!(f, "[_]"),
        }
    }
}

pub struct Lexer<'t> {
    source: &'t str,
    iter: Peekable<Chars<'t>>,
    curr_char: Option<char>,
    location: Location,
}

impl<'t> Lexer<'t> {
    pub fn new(source: &'t str) -> Self {
        Self {
            source,
            iter: source.chars().peekable(),
            curr_char: None,
            location: Location { line: 1, column: 1 },
            previous_location: Location { line: 1, column: 1 },
        }
    }

    fn next_char(&mut self) -> Option<char> {
        self.curr_char = self.iter.next();

        match self.curr_char {
            Some('\n') => {
                self.location.column = 1;
                self.location.line += 1;
            }
            Some(_) => self.location.column += 1,
            _ => (),
        }

        self.curr_char
    }

    fn peek_char(&mut self) -> Option<char> {
        self.iter.peek().map(|c| c.to_owned())
    }

    fn skip_whitespaces_and_comments(&mut self) {
        while let Some(c) = self.next_char() {
            match c {
                '#' => self.skip_line_comment(),
                '/' => match self.next_char() {
                    Some('/') => self.skip_line_comment(),
                    Some('*') => self.skip_multiline_comment(),
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
    fn make_string(&mut self, location: Location) -> Result<Token> {
        let mut string = String::new();

        loop {
            match self.next_char() {
                None => return Err(Error::expected(vec!["\""], self.location.clone())),
                Some('"') => return Ok(Token::String(location, string)),
                Some('\\') => match self.next_char() {
                    None => return Err(Error::expected(vec!["\"", "\\"], self.location.clone())),
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
    fn make_block_string(&mut self, location: Location) -> Result<Token> {
        let delimiter = self.next_char();
        if delimiter.is_none() {
            return Err(Error::expected_any_char(location));
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
                c if c == delimiter => return Ok(Token::String(location, string)),
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
                c if c == delimiter => break,
                c if c.is_whitespace() && whitespaces_left > 0 => whitespaces_left -= 1,
                c => {
                    string.push(c);
                    whitespaces_left = 0;
                }
            }
        }

        Ok(Token::String(location, string))
    }

    /// Creates a 32 bits unsigned number token.
    fn make_number(&mut self, location: Location) -> Result<Token> {
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
        Ok(Token::Integer(location, number))
    }

    /// Creates either a keyword token or an identifier one.
    fn make_identifier(&mut self, location: Location) -> Result<Token> {
        let mut string = String::from(self.curr_char.unwrap());

        while let Some(c) = self.peek_char() {
            if c.is_alphanumeric() || c == '_' {
                self.next_char();
                string.push(c);
            } else {
                break;
            }
        }

        Ok(match string.as_str() {
            "and" => Token::And(location),
            "continue" => Token::Continue(location),
            "fail" => Token::Fail(location),
            "fn" => Token::Fn(location),
            "fork" => Token::Fork(location),
            "join" => Token::Join(location),
            "let" => Token::Let(location),
            "match" => Token::Match(location),
            "null" => Token::Null(location),
            "or" => Token::Or(location),
            _ => Token::Identifier(location, string),
        })
    }
}

impl<'t> Iterator for Lexer<'t> {
    type Item = Result<Token>;

    fn next(&mut self) -> Option<Self::Item> {
        self.skip_whitespaces_and_comments();

        let loc = self.location.clone();

        let token = match self.curr_char? {
            '&' => Ok(Token::Amp(loc)),
            ',' => Ok(Token::Comma(loc)),
            '.' => Ok(Token::Dot(loc)),
            '=' => match self.next_char() {
                Some('=') => Ok(Token::EqualEqual(loc)),
                Some('>') => Ok(Token::EqualGt(loc)),
                _ => Ok(Token::Equal(loc)),
            },
            '!' => match self.next_char() {
                Some('=') => Ok(Token::ExclamEqual(loc)),
                Some('~') => Ok(Token::ExclamTilde(loc)),
                Some(c) => Err(Error::expected_but_got(vec!["=", "~"], &c, loc)),
                None => Err(Error::expected(vec!["=", "~"], loc)),
            },
            '{' => Ok(Token::LeftBrace(loc)),
            '[' => Ok(Token::LeftBracket(loc)),
            '|' => Ok(Token::Pipe(loc)),
            '}' => Ok(Token::RightBrace(loc)),
            ']' => Ok(Token::RightBracket(loc)),
            ';' => Ok(Token::Semicolon(loc)),
            '~' => Ok(Token::Tilde(loc)),
            '_' => Ok(Token::Underscore(loc)),
            '"' => match self.peek_char() {
                Some('"') => {
                    self.next_char();
                    match self.peek_char() {
                        Some('"') => {
                            self.next_char();
                            self.make_block_string(loc)
                        }
                        _ => Ok(Token::String(loc, "".to_string())),
                    }
                }
                _ => self.make_string(loc),
            },
            c if c.is_ascii_digit() => self.make_number(loc),
            c if c.is_alphabetic() => self.make_identifier(loc),
            c => {
                let mut loc = loc;
                loc.column -= 1;
                Err(Error::unexpected(&c, loc))
            }
        };

        Some(token)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn skip_whitespaces() {
        let mut lexer = Lexer::new(" ");
        let token = lexer.next();
        assert!(token.is_none());
    }

    #[test]
    fn skip_c_line_comment() {
        let mut lexer = Lexer::new("// [\n]");
        let token = lexer.next();
        assert!(token.is_some());
        let token = token.unwrap();
        assert!(token.is_ok());
        let token = token.unwrap();
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn skip_shell_line_comment() {
        let mut lexer = Lexer::new("# [\n]");
        let token = lexer.next();
        assert!(token.is_some());
        let token = token.unwrap();
        assert!(token.is_ok());
        let token = token.unwrap();
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn skip_multiline_comment() {
        let mut lexer = Lexer::new("/*\n[ */ ]");
        let token = lexer.next();
        assert!(token.is_some());
        let token = token.unwrap();
        assert!(token.is_ok());
        let token = token.unwrap();
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn unexpected() {
        let mut lexer = Lexer::new("§");

        let token = lexer.next();
        assert!(token.is_some());

        let token = token.unwrap();

        // todo
        // assert_enum!(token, Token::Error(loc, error), {
        //     assert_eq!(Location::new(1, 1), loc);
        //     assert_eq!("unexpected `§`", error);
        // });

        assert!(if let Err(err) = token {
            assert_eq!(err.location, Location { line: 1, column: 1 });
            assert_eq!(err.error, "unexpected `§`");
            true
        } else {
            false
        });
    }

    macro_rules! empty_token {
        ($($name:ident: $str:expr => $token:pat,)*) => {
        $(
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($str);
                let token = lexer.next();
                assert!(token.is_some());
                let token = token.unwrap();
                assert!(token.is_ok());
                let token = token.unwrap();
                assert!(matches!(token, $token));
            }
        )*
        }
    }

    empty_token! {
        token_amp:              "&"         => Token::Amp(_),
        token_and:              "and"       => Token::And(_),
        token_comma:            ","         => Token::Comma(_),
        token_continue:         "continue"  => Token::Continue(_),
        token_dot:              "."         => Token::Dot(_),
        token_equal:            "="         => Token::Equal(_),
        token_equal_equal:      "=="        => Token::EqualEqual(_),
        token_equal_gt:         "=>"        => Token::EqualGt(_),
        token_exclam_equal:     "!="        => Token::ExclamEqual(_),
        token_exclam_tilde:     "!~"        => Token::ExclamTilde(_),
        token_fail:             "fail"      => Token::Fail(_),
        token_fn:               "fn"        => Token::Fn(_),
        token_fork:             "fork"      => Token::Fork(_),
        token_join:             "join"      => Token::Join(_),
        token_left_brace:       "{"         => Token::LeftBrace(_),
        token_left_bracket:     "["         => Token::LeftBracket(_),
        token_let:              "let"       => Token::Let(_),
        token_match:            "match"     => Token::Match(_),
        token_null:             "null"      => Token::Null(_),
        token_or:               "or"        => Token::Or(_),
        token_pipe:             "|"         => Token::Pipe(_),
        token_right_brace:      "}"         => Token::RightBrace(_),
        token_right_bracket:    "]"         => Token::RightBracket(_),
        token_semicolon:        ";"         => Token::Semicolon(_),
        token_tilde:            "~"         => Token::Tilde(_),
        token_underscore:       "_"         => Token::Underscore(_),
    }

    #[test]
    fn sequence_dot_equal() {
        let mut lexer = Lexer::new(".=");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Equal(_)))));
    }

    #[test]
    fn sequence_empty_string_dot() {
        let mut lexer = Lexer::new("\"\".");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::String(_, _)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
    }

    #[test]
    fn sequence_string_dot() {
        let mut lexer = Lexer::new("\"str\".");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::String(_, _)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
    }

    #[test]
    fn sequence_block_string_dot() {
        let mut lexer = Lexer::new("\"\"\";\nline1;.");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::String(_, _)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
    }

    #[test]
    fn sequence_identifier_dot() {
        let mut lexer = Lexer::new("identifier.");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Identifier(_, _)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
    }

    #[test]
    fn sequence_integer_dot() {
        let mut lexer = Lexer::new("200.");
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Integer(_, _)))));
        let token = lexer.next();
        assert!(matches!(token, Some(Ok(Token::Dot(_)))));
    }

    #[test]
    fn exclam_nothing() {
        let mut lexer = Lexer::new("!");

        let token = lexer.next();
        assert!(token.is_some());

        let token = token.unwrap();
        // todo (see unexpected)
        assert!(if let Err(err) = token {
            assert_eq!(err.location, Location { line: 1, column: 2 });
            assert_eq!(err.error, "expected `=` or `~`, got nothing");
            true
        } else {
            false
        });
    }

    #[test]
    fn exclam_something() {
        let mut lexer = Lexer::new("!a");

        let token = lexer.next();
        assert!(token.is_some());

        let token = token.unwrap();
        // todo (see unexpected)
        assert!(if let Err(err) = token {
            assert_eq!(err.location, Location { line: 1, column: 2 });
            assert_eq!(err.error, "expected `=` or `~`, got `a`");
            true
        } else {
            false
        });
    }

    macro_rules! string {
        ($($name:ident: $strin:expr => $strout:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($strin);
                let token = lexer.next();
                assert!(token.is_some());
                let token = token.unwrap();
                assert!(token.is_ok());
                let token = token.unwrap();
                assert!(if let Token::String(_, string) = token {
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
        let token = lexer.next();
        assert!(token.is_some());
        let token = token.unwrap();
        assert!(token.is_ok());
        let token = token.unwrap();
        assert!(if let Token::Integer(_, integer) = token {
            assert_eq!(integer, 200);
            true
        } else {
            false
        });
    }

    #[test]
    fn identifier() {
        let mut lexer = Lexer::new("identifier");
        let token = lexer.next();
        assert!(token.is_some());
        let token = token.unwrap();
        assert!(token.is_ok());
        let token = token.unwrap();
        assert!(if let Token::Identifier(_, identifier) = token {
            assert_eq!(identifier, "identifier");
            true
        } else {
            false
        });
    }
}
