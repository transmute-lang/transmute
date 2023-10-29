use crate::lexer::{Location, Span};
use std::fmt::{Display, Formatter};

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

    pub fn name(&self) -> &str {
        &self.name
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}
