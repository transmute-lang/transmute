use crate::lexer::Span;

#[derive(Debug)]
pub enum Error {
    NoMatch,
    UnexpectedChar(Span),
    ExpectedSemicolon(Span),
}
