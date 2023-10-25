use crate::parser::Literal;

pub trait Visitor<R> {
    fn visit(&mut self, ast: &Ast) -> R;
}

#[derive(Debug, PartialEq)]
pub struct Ast {
    pub root: Literal,
}

impl Ast {
    pub fn accept<V, R>(&self, visitor: &mut V) -> R
    where
        V: Visitor<R>,
    {
        visitor.visit(self)
    }
}
