use std::cmp::Ordering;
use std::fmt::{Debug, Formatter};

#[derive(Default, Clone, Eq)]
pub struct Span {
    pub line: usize,
    pub column: usize,
    pub start: usize,
    pub len: usize,
}

impl Span {
    pub fn new(line: usize, column: usize, start: usize, len: usize) -> Self {
        assert!(line >= 1);
        assert!(column >= 1);
        Self {
            line,
            column,
            start,
            len,
        }
    }

    pub fn extend_to(&self, other: &Span) -> Self {
        let self_end = self.start + self.len;
        let other_end = other.start + other.len;
        let diff = other_end - self_end;
        Self {
            line: self.line,
            column: self.column,
            start: self.start,
            len: self.len + diff,
        }
    }

    pub fn extend(&self, len: usize) -> Self {
        Self {
            line: self.line,
            column: self.column,
            start: self.start,
            len: self.len + len,
        }
    }

    pub fn end(&self) -> usize {
        self.start + self.len
    }
}

impl PartialEq<Self> for Span {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.len == other.len
    }
}

impl PartialOrd<Self> for Span {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Span {
    fn cmp(&self, other: &Self) -> Ordering {
        if self == other {
            return Ordering::Equal;
        }
        if self.start < other.start {
            return Ordering::Less;
        }
        if self.start == other.start && self.len < other.len {
            return Ordering::Less;
        }
        Ordering::Greater
    }
}

impl Debug for Span {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}:{}; [{}, {}]",
            self.line,
            self.column,
            self.start,
            self.start + self.len
        )
    }
}
