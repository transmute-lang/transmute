use crate::ids::SymbolId;
use std::fmt::{Debug, Formatter};

pub trait BoundState {}

#[derive(Debug, Clone, PartialEq)]
pub struct Unbound;

impl BoundState for Unbound {}

#[derive(Clone, PartialEq)]
pub struct Bound(pub SymbolId);

impl BoundState for Bound {}

impl Debug for Bound {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bound({})", self.0)
    }
}
