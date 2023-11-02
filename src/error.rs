use crate::lexer::Span;

#[derive(Debug)]
pub enum Error {
    UnexpectedEof,
    NoMatch,
    UnexpectedChar(Span),
    ExpectedSemicolon(Span),
}
