use crate::lexer::{Span, Token};

#[derive(Debug)]
pub enum Error {
    UnexpectedEof,
    NoMatch,
    UnexpectedChar(char, Span),
    ExpectedSemicolon(Token),
}
