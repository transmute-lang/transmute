use crate::input::Inputs;
use crate::span::Span;
use std::fmt::{Debug, Display, Formatter};

#[derive(Debug, Default, PartialEq)]
pub struct Diagnostics<I> {
    diagnostics: Vec<Diagnostic>,
    inputs: I,
}

impl<I> Diagnostics<I> {
    pub fn len(&self) -> usize {
        self.diagnostics.len()
    }

    pub fn is_empty(&self) -> bool {
        self.diagnostics.is_empty()
    }

    pub fn iter(&self) -> DiagnosticsIterator<I> {
        DiagnosticsIterator {
            diagnostics: self,
            index: 0,
        }
    }

    pub fn append(&mut self, mut other: Self) {
        self.diagnostics.append(&mut other.diagnostics)
    }

    pub fn push(&mut self, diagnostic: Diagnostic) {
        self.diagnostics.push(diagnostic);
    }

    pub fn report_err<S: Into<String>>(
        &mut self,
        message: S,
        span: Span,
        generated_at: (&'static str, u32),
    ) {
        self.push(Diagnostic::new(message, span, Level::Error, generated_at));
    }
}

impl Diagnostics<()> {
    pub fn with_inputs(self, inputs: Inputs) -> Diagnostics<Inputs> {
        Diagnostics {
            diagnostics: self.diagnostics,
            inputs,
        }
    }
}

impl Display for Diagnostics<()> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut diagnostics = self.diagnostics.to_vec();
        diagnostics.sort_by(|a, b| a.span.cmp(&b.span));

        for diagnostic in diagnostics {
            writeln!(f, " - {}", diagnostic)?;
        }
        Ok(())
    }
}

impl Display for Diagnostics<Inputs> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut diagnostics = self.diagnostics.to_vec();
        diagnostics.sort_by(|a, b| a.span.cmp(&b.span));

        for diagnostic in diagnostics {
            writeln!(f, " - {}", diagnostic.format(&self.inputs))?;
        }
        Ok(())
    }
}

pub struct DiagnosticsIterator<'a, I> {
    diagnostics: &'a Diagnostics<I>,
    index: usize,
}

impl<'a, I> Iterator for DiagnosticsIterator<'a, I> {
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

#[derive(Clone, PartialEq)]
pub struct Diagnostic {
    pub message: String,
    pub span: Span,
    pub level: Level,
    pub generated_at: (&'static str, u32),
}

impl Diagnostic {
    pub fn format(&self, inputs: &Inputs) -> String {
        #[cfg(debug_assertions)]
        {
            format!(
                "[{generated_at_file}:{generated_at_line}] {source}:{line}:{column}: {message}",
                generated_at_file = self.generated_at.0,
                generated_at_line = self.generated_at.1,
                message = self.message,
                source = inputs[self.span.input_id].name(),
                line = self.span.line,
                column = self.span.column
            )
        }
        #[cfg(not(debug_assertions))]
        {
            format!(
                "{}:{}:{}: {}",
                self.message,
                inputs[self.span.input_id].name(),
                self.span.line,
                self.span.column
            )
        }
    }
}

impl Display for Diagnostic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        #[cfg(debug_assertions)]
        {
            write!(
                f,
                "[{generated_at_file}:{generated_at_line}] {line}:{column}: {message}",
                generated_at_file = self.generated_at.0,
                generated_at_line = self.generated_at.1,
                message = self.message,
                line = self.span.line,
                column = self.span.column
            )
        }
        #[cfg(not(debug_assertions))]
        {
            write!(
                f,
                "{}:{}: {}",
                self.span.line, self.span.column, self.message
            )
        }
    }
}

impl Debug for Diagnostic {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Diagnostic {{")?;
        writeln!(f, "    message: {:?},", self.message)?;
        writeln!(f, "    span: {:?},", self.span)?;
        writeln!(f, "    level: {:?},", self.level)?;
        #[cfg(feature = "print_generated_at_in_diagnostic_debug")]
        {
            writeln!(
                f,
                "    generated_at: {}:{},",
                self.generated_at.0, self.generated_at.1
            )?;
        }
        write!(f, "}}")
    }
}

impl Diagnostic {
    pub fn new<S: Into<String>>(
        message: S,
        span: Span,
        level: Level,
        generated_at: (&'static str, u32),
    ) -> Self {
        Self {
            message: message.into(),
            span,
            level,
            generated_at,
        }
    }

    pub fn error<S: Into<String>>(
        message: S,
        span: Span,
        generated_at: (&'static str, u32),
    ) -> Self {
        Self::new(message, span, Level::Error, generated_at)
    }
}

#[derive(Debug, Clone, Copy, Ord, PartialOrd, Eq, PartialEq)]
pub enum Level {
    Error,
}
