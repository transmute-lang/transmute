use std::fmt::{Debug, Display, Formatter};
use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug)]
pub enum ErrorKind {
    ExpectedOneOf(Vec<String>),
    ExpectedAny(),
    Unexpected(char),
    UnterminatedString(),
}

#[derive(Debug)]
pub struct Error {
    location: Location,
    kind: ErrorKind,
}

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

pub enum Token {
    And(Location),
    Comma(Location),
    Continue(Location),
    Dot(Location),
    Eof(Location),
    Equal(Location),
    EqualEqual(Location),
    EqualGt(Location),
    Exclam(Location),
    ExclamEqual(Location),
    ExclamTilde(Location),
    Fail(Location),
    Fn(Location),
    Fork(Location),
    Gt(Location),
    GtEqual(Location),
    Identifier(Location, String),
    Integer(Location, u32),
    Invalid(Location, ErrorKind),
    Join(Location),
    LeftBrace(Location),
    LeftBracket(Location),
    LeftParenthesis(Location),
    Let(Location),
    Lt(Location),
    LtEqual(Location),
    Match(Location),
    Minus(Location),
    Null(Location),
    Or(Location),
    Percent(Location),
    Pipe(Location),
    Plus(Location),
    RightBrace(Location),
    RightBracket(Location),
    RightParenthesis(Location),
    Semicolon(Location),
    Slash(Location),
    Star(Location),
    String(Location, String),
    Tilde(Location),
    Underscore(Location),
}

impl Token {
    pub fn location(&self) -> &Location {
        use Token::*;
        match self {
            And(loc) => loc,
            Comma(loc) => loc,
            Continue(loc) => loc,
            Dot(loc) => loc,
            Eof(loc) => loc,
            Equal(loc) => loc,
            EqualEqual(loc) => loc,
            EqualGt(loc) => loc,
            Exclam(loc) => loc,
            ExclamEqual(loc) => loc,
            ExclamTilde(loc) => loc,
            Fail(loc) => loc,
            Fn(loc) => loc,
            Fork(loc) => loc,
            Gt(loc) => loc,
            GtEqual(loc) => loc,
            Identifier(loc, _) => loc,
            Integer(loc, _) => loc,
            Invalid(loc, _) => loc,
            Join(loc) => loc,
            LeftBrace(loc) => loc,
            LeftBracket(loc) => loc,
            LeftParenthesis(loc) => loc,
            Let(loc) => loc,
            Lt(loc) => loc,
            LtEqual(loc) => loc,
            Match(loc) => loc,
            Minus(loc) => loc,
            Null(loc) => loc,
            Or(loc) => loc,
            Percent(loc) => loc,
            Pipe(loc) => loc,
            Plus(loc) => loc,
            RightBrace(loc) => loc,
            RightBracket(loc) => loc,
            RightParenthesis(loc) => loc,
            Semicolon(loc) => loc,
            Slash(loc) => loc,
            Star(loc) => loc,
            String(loc, _) => loc,
            Tilde(loc) => loc,
            Underscore(loc) => loc,
        }
    }
}

impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Token::*;
        match self {
            And(_) => write!(f, "[and]"),
            Comma(_) => write!(f, "[,]"),
            Continue(_) => write!(f, "[continue]"),
            Dot(_) => write!(f, "[.]"),
            Eof(_) => write!(f, "[EOF]"),
            Equal(_) => write!(f, "[=]"),
            EqualEqual(_) => write!(f, "[==]"),
            EqualGt(_) => write!(f, "[=>]"),
            Exclam(_) => write!(f, "[!]"),
            ExclamEqual(_) => write!(f, "[!=]"),
            ExclamTilde(_) => write!(f, "[!~]"),
            Fail(_) => write!(f, "[fail]"),
            Fn(_) => write!(f, "[fn]"),
            Fork(_) => write!(f, "[fork]"),
            Gt(_) => write!(f, "[>]"),
            GtEqual(_) => write!(f, "[>=]"),
            Identifier(_, value) => write!(f, "[identifier:{}]", value),
            Integer(_, value) => write!(f, "[integer:{}]", value),
            Invalid(_, value) => write!(f, "[invalid:{:?}]", value),
            Join(_) => write!(f, "[join]"),
            LeftBrace(_) => write!(f, "[{{]"),
            LeftBracket(_) => write!(f, "[[]"),
            LeftParenthesis(_) => write!(f, "[(]"),
            Let(_) => write!(f, "[let]"),
            Lt(_) => write!(f, "[<]"),
            LtEqual(_) => write!(f, "[<=]"),
            Match(_) => write!(f, "[match]"),
            Minus(_) => write!(f, "[-]"),
            Null(_) => write!(f, "[null]"),
            Or(_) => write!(f, "[or]"),
            Percent(_) => write!(f, "[%]"),
            Pipe(_) => write!(f, "[|]"),
            Plus(_) => write!(f, "[+]"),
            RightBrace(_) => write!(f, "[}}]"),
            RightBracket(_) => write!(f, "[]]"),
            RightParenthesis(_) => write!(f, "[)]"),
            Semicolon(_) => write!(f, "[;]"),
            Slash(_) => write!(f, "[/]"),
            Star(_) => write!(f, "[*]"),
            String(_, value) => write!(f, "[string:{}]", value),
            Tilde(_) => write!(f, "[~]"),
            Underscore(_) => write!(f, "[_]"),
        }
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use Token::*;
        match self {
            And(_) => write!(f, "and"),
            Comma(_) => write!(f, ","),
            Continue(_) => write!(f, "continue"),
            Dot(_) => write!(f, "."),
            Eof(_) => write!(f, "EOF"),
            Equal(_) => write!(f, "="),
            EqualEqual(_) => write!(f, "=="),
            EqualGt(_) => write!(f, "=>"),
            Exclam(_) => write!(f, "!"),
            ExclamEqual(_) => write!(f, "!="),
            ExclamTilde(_) => write!(f, "!~"),
            Fail(_) => write!(f, "fail"),
            Fn(_) => write!(f, "fn"),
            Fork(_) => write!(f, "fork"),
            Gt(_) => write!(f, ">"),
            GtEqual(_) => write!(f, ">="),
            Identifier(_, _) if f.alternate() => write!(f, "identifier"),
            Identifier(_, value) => write!(f, "{}", value),
            Integer(_, _) if f.alternate() => write!(f, "integer"),
            Integer(_, value) => write!(f, "{}", value),
            Invalid(_, _) if f.alternate() => write!(f, "invalid"),
            Invalid(_, value) => match value {
                ErrorKind::UnterminatedString() => write!(f, "UNTERMINATED_STRING"),
                ErrorKind::Unexpected(c) => write!(f, "_{}_", c),
                // todo find better representation
                ErrorKind::ExpectedAny() => write!(f, "ANY"),
                // todo find better representation
                ErrorKind::ExpectedOneOf(v) => write!(f, "({})", v.join(", ")),
            },
            Join(_) => write!(f, "join"),
            LeftBrace(_) => write!(f, "{{"),
            LeftBracket(_) => write!(f, "["),
            LeftParenthesis(_) => write!(f, "("),
            Let(_) => write!(f, "let"),
            Lt(_) => write!(f, "<"),
            LtEqual(_) => write!(f, "<="),
            Match(_) => write!(f, "match"),
            Minus(_) => write!(f, "-"),
            Null(_) => write!(f, "null"),
            Or(_) => write!(f, "or"),
            Percent(_) => write!(f, "%"),
            Pipe(_) => write!(f, "|"),
            Plus(_) => write!(f, "+"),
            RightBrace(_) => write!(f, "}}"),
            RightBracket(_) => write!(f, "]"),
            RightParenthesis(_) => write!(f, ")"),
            Semicolon(_) => write!(f, ";"),
            Slash(_) => write!(f, "/"),
            Star(_) => write!(f, "*"),
            String(_, _) if f.alternate() => write!(f, "string"),
            String(_, value) => write!(f, "{}", value),
            Tilde(_) => write!(f, "~"),
            Underscore(_) => write!(f, "_"),
        }
    }
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
                    return Token::Invalid(self.location.clone(), ErrorKind::UnterminatedString())
                }
                Some('"') => return Token::String(location, string),
                Some('\\') => match self.next_char() {
                    None => {
                        return Token::Invalid(
                            Location {
                                line: self.location.line,
                                column: self.location.column + 1,
                            },
                            ErrorKind::ExpectedOneOf(vec!["\"".to_string(), "\\".to_string()]),
                        );
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
            return Token::Invalid(location, ErrorKind::ExpectedAny());
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
                c if c == delimiter => return Token::String(location, string),
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
                c if c == delimiter => return Token::String(location, string),
                c if c.is_whitespace() && whitespaces_left > 0 => whitespaces_left -= 1,
                c => {
                    string.push(c);
                    whitespaces_left = 0;
                }
            }
        }

        Token::Invalid(location, ErrorKind::UnterminatedString())
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
        Token::Integer(location, number)
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

        let loc = self.location.clone();

        let token = match self.curr_char {
            Some(';') => Token::Semicolon(loc),
            Some(',') => Token::Comma(loc),
            Some('_') => Token::Underscore(loc),
            Some('|') => Token::Pipe(loc),
            Some('.') => Token::Dot(loc),
            Some('+') => Token::Plus(loc),
            Some('-') => Token::Minus(loc),
            Some('*') => Token::Star(loc),
            Some('/') => Token::Slash(loc),
            Some('%') => Token::Percent(loc),
            Some('~') => Token::Tilde(loc),
            Some('=') => match next_char_if!(self, '=', '>') {
                Some('=') => Token::EqualEqual(loc),
                Some('>') => Token::EqualGt(loc),
                _ => Token::Equal(loc),
            },
            Some('!') => match next_char_if!(self, '=', '~') {
                Some('=') => Token::ExclamEqual(loc),
                Some('~') => Token::ExclamTilde(loc),
                _ => Token::Exclam(loc),
            },
            Some('(') => Token::LeftParenthesis(loc),
            Some(')') => Token::RightParenthesis(loc),
            Some('{') => Token::LeftBrace(loc),
            Some('}') => Token::RightBrace(loc),
            Some('[') => Token::LeftBracket(loc),
            Some(']') => Token::RightBracket(loc),
            Some('>') => match next_char_if!(self, '=') {
                Some('=') => Token::GtEqual(loc),
                _ => Token::Gt(loc),
            },
            Some('<') => match next_char_if!(self, '=') {
                Some('=') => Token::LtEqual(loc),
                _ => Token::Lt(loc),
            },
            Some('"') => match next_char_if!(self, '"') {
                Some('"') => match next_char_if!(self, '"') {
                    Some('"') => self.make_block_string(loc),
                    _ => Token::String(loc, "".to_string()),
                },
                _ => self.make_string(loc),
            },
            Some(c) if c.is_ascii_digit() => self.make_number(loc),
            Some(c) if c.is_alphabetic() => self.make_identifier(loc),
            Some(c) => Token::Invalid(loc, ErrorKind::Unexpected(c)),
            None if !self.eof => {
                self.eof = true;
                return Some(Token::Eof(Location::new(loc.line, loc.column + 1)));
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
        assert!(matches!(token, Token::Eof(Location { line: 1, column: 1 })));

        let token = lexer.next();
        assert!(token.is_none());
    }

    #[test]
    fn skip_whitespaces() {
        let mut lexer = Lexer::new(" ");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(token, Token::Eof(Location { line: 1, column: 2 })));
    }

    #[test]
    fn skip_c_line_comment() {
        let mut lexer = Lexer::new("// [\n]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn skip_shell_line_comment() {
        let mut lexer = Lexer::new("# [\n]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn skip_multiline_comment() {
        let mut lexer = Lexer::new("/*\n[ */ ]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn skip_empty_multiline_comment() {
        let mut lexer = Lexer::new("/**/]");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(token, Token::RightBracket(_)));
    }

    #[test]
    fn unexpected() {
        let mut lexer = Lexer::new("§");
        let token = lexer.next().expect("expected Some");
        assert!(matches!(
            token,
            Token::Invalid(Location { line: 1, column: 1 }, ErrorKind::Unexpected('§'))
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
        token_and:               "and"       => Token::And(_),
        token_comma:             ","         => Token::Comma(_),
        token_continue:          "continue"  => Token::Continue(_),
        token_dot:               "."         => Token::Dot(_),
        token_eof:               ""          => Token::Eof(_),
        token_equal:             "="         => Token::Equal(_),
        token_equal_equal:       "=="        => Token::EqualEqual(_),
        token_equal_gt:          "=>"        => Token::EqualGt(_),
        token_exclam:            "!"         => Token::Exclam(_),
        token_exclam_equal:      "!="        => Token::ExclamEqual(_),
        token_exclam_tilde:      "!~"        => Token::ExclamTilde(_),
        token_fail:              "fail"      => Token::Fail(_),
        token_fn:                "fn"        => Token::Fn(_),
        token_fork:              "fork"      => Token::Fork(_),
        token_gt:                ">"         => Token::Gt(_),
        token_gt_equal:          ">="        => Token::GtEqual(_),
        token_join:              "join"      => Token::Join(_),
        token_left_brace:        "{"         => Token::LeftBrace(_),
        token_left_bracket:      "["         => Token::LeftBracket(_),
        token_left_parenthesis:  "("         => Token::LeftParenthesis(_),
        token_let:               "let"       => Token::Let(_),
        token_lt:                "<"         => Token::Lt(_),
        token_lt_equal:          "<="        => Token::LtEqual(_),
        token_match:             "match"     => Token::Match(_),
        token_minus:             "-"         => Token::Minus(_),
        token_null:              "null"      => Token::Null(_),
        token_or:                "or"        => Token::Or(_),
        token_percent:           "%"         => Token::Percent(_),
        token_pipe:              "|"         => Token::Pipe(_),
        token_plus:              "+"         => Token::Plus(_),
        token_right_brace:       "}"         => Token::RightBrace(_),
        token_right_bracket:     "]"         => Token::RightBracket(_),
        token_right_parenthesis: ")"         => Token::RightParenthesis(_),
        token_semicolon:         ";"         => Token::Semicolon(_),
        token_slash:             "/"         => Token::Slash(_),
        token_star:              "*"         => Token::Star(_),
        token_tilde:             "~"         => Token::Tilde(_),
        token_underscore:        "_"         => Token::Underscore(_),
        token_loc_1_1:           "+"         => Token::Plus(Location{line:1,column:1}),
        token_loc_2_1:           "\n+"       => Token::Plus(Location{line:2,column:1}),
        token_loc_1_2:           " +"        => Token::Plus(Location{line:1,column:2}),
        token_loc_2_2:           "\n +"      => Token::Plus(Location{line:2,column:2}),
    }

    #[test]
    fn sequence_dot_equal() {
        let mut lexer = Lexer::new(".=");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Equal(_))));
    }

    #[test]
    fn sequence_empty_string_dot() {
        let mut lexer = Lexer::new("\"\".");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::String(_, _))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_string_dot() {
        let mut lexer = Lexer::new("\"str\".");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::String(_, _))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_block_string_dot() {
        let mut lexer = Lexer::new("\"\"\";\nline1;.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::String(_, _))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_identifier_dot() {
        let mut lexer = Lexer::new("identifier.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Identifier(_, _))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_integer_dot() {
        let mut lexer = Lexer::new("200.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Integer(_, _))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_exclam_dot() {
        let mut lexer = Lexer::new("!.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Exclam(_))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_equal_dot() {
        let mut lexer = Lexer::new("=.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Equal(_))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_gt_dot() {
        let mut lexer = Lexer::new(">.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Gt(_))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    #[test]
    fn sequence_lt_dot() {
        let mut lexer = Lexer::new("<.");
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Lt(_))));
        let token = lexer.next();
        assert!(matches!(token, Some(Token::Dot(_))));
    }

    macro_rules! string {
        ($($name:ident: $strin:expr => $strout:expr,)*) => {
        $(
            #[test]
            fn $name() {
                let mut lexer = Lexer::new($strin);
                let token = lexer.next().expect("expected Some");
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
        let token = lexer.next().expect("expected Some");
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
        let token = lexer.next().expect("expected Some");
        assert!(if let Token::Identifier(_, identifier) = token {
            assert_eq!(identifier, "identifier");
            true
        } else {
            false
        });
    }
}
