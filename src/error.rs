use crate::lexer::Span;

#[derive(Debug)]
pub enum Error {
    NoMatch,
    UnexpectedChar(Span),
    ExpectedSemicolon(Span),
}

#[derive(Debug, Default, PartialEq)]
pub struct Diagnostics {
    diagnostics: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    pub fn report_err<S: Into<String>>(&mut self, message: S, span: Span) {
        self.diagnostics.push(Diagnostic {
            message: message.into(),
            span,
            level: Level::Error,
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct Diagnostic {
    message: String,
    span: Span,
    level: Level,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Level {
    Error,
}
