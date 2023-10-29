use crate::lexer::{Location, Span};

#[derive(Debug, PartialEq)]
pub struct Identifier {
    name: String,
    location: Location,
    span: Span,
}

impl Identifier {
    pub fn new(name: String, location: Location, span: Span) -> Self {
        Self {
            name,
            location,
            span,
        }
    }

    pub fn location(&self) -> &Location {
        &self.location
    }

    pub fn span(&self) -> &Span {
        &self.span
    }
}
