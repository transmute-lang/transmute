use crate::lexer::Span;
use std::fmt::{Display, Formatter};

#[derive(Debug)]
pub enum Error {
    // NoMatch,
    UnexpectedChar(Span),
    ExpectedSemicolon(Span),
}

#[derive(Debug, Default, PartialEq)]
pub struct Diagnostics {
    diagnostics: Vec<Diagnostic>,
}

impl Diagnostics {
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    pub fn iter(&self) -> DiagnosticsIterator {
        DiagnosticsIterator {
            diagnostics: self,
            index: 0,
        }
    }

    pub fn append(&mut self, mut other: Self) {
        self.diagnostics.append(&mut other.diagnostics)
    }

    pub fn report_err<S: Into<String>>(
        &mut self,
        message: S,
        span: Span,
        generated_at: (&'static str, u32),
    ) {
        self.diagnostics.push(Diagnostic {
            message: message.into(),
            span,
            level: Level::Error,
            generated_at,
        })
    }
}

impl Display for Diagnostics {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut diagnostics = self.diagnostics.to_vec();
        diagnostics.sort_by(|a, b| a.span.cmp(&b.span));

        for diagnostic in diagnostics {
            writeln!(
                f,
                "[{}:{}] {} at {}:{}",
                diagnostic.generated_at.0,
                diagnostic.generated_at.1,
                diagnostic.message,
                diagnostic.span.line(),
                diagnostic.span.column()
            )?;
        }
        Ok(())
    }
}

pub struct DiagnosticsIterator<'a> {
    diagnostics: &'a Diagnostics,
    index: usize,
}

impl<'a> Iterator for DiagnosticsIterator<'a> {
    type Item = &'a Diagnostic;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.diagnostics.len() {
            self.index += 1;
            Some(&self.diagnostics.diagnostics[self.index - 1])
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Diagnostic {
    message: String,
    span: Span,
    level: Level,
    generated_at: (&'static str, u32),
}

impl Diagnostic {
    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn level(&self) -> Level {
        self.level
    }
}

#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
pub enum Level {
    Error,
}
