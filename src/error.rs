use crate::lexer::{Location, Span};

#[derive(Debug)]
pub enum Error {
    UnexpectedEof,
    NoMatch,
    UnexpectedChar(char, Location, Span),
}
