use std::fmt::{Debug, Formatter};
use transmute_core::ids::SymbolId;

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

#[derive(PartialEq)]
pub struct BoundMultiple(pub Vec<SymbolId>);

impl BoundState for BoundMultiple {}

impl Debug for BoundMultiple {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Bound({:?})", self.0)
    }
}
