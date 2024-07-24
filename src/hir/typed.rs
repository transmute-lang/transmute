use crate::ids::TypeId;
use std::fmt::{Debug, Formatter};

pub trait TypedState {}

#[derive(Debug)]
pub struct Untyped;

impl TypedState for Untyped {}

#[derive(Clone)]
pub struct Typed(pub TypeId);

impl TypedState for Typed {}

impl Debug for Typed {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Typed({})", self.0)
    }
}
