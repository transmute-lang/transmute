use crate::lexer::Span;
use std::fmt::{Display, Formatter};

#[derive(Debug, PartialEq)]
pub struct Identifier<'s> {
    name: &'s str,
    span: Span,
}

impl<'s> Identifier<'s> {
    pub fn new(name: &'s str, span: Span) -> Self {
        Self { name, span }
    }

    pub fn span(&self) -> &Span {
        &self.span
    }

    pub fn name(&self) -> &str {
        self.name
    }
}

impl Display for Identifier<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
