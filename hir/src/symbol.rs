use crate::natives::{NativeFnKind, Type};
use transmute_core::ids::{IdentId, StmtId, SymbolId, TypeId};

#[derive(Debug, PartialEq)]
pub struct Symbol {
    pub id: SymbolId,
    pub kind: SymbolKind,
    pub type_id: TypeId,
}

impl Symbol {
    pub fn as_function(&self) -> (&Vec<TypeId>, TypeId) {
        match &self.kind {
            SymbolKind::LetFn(_, params, ret_type_id) => (params, *ret_type_id),
            _ => panic!("{:?} is not a function", self),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    // fixme can we remove it? at least in mir
    NotFound,
    Let(StmtId),
    LetFn(StmtId, Vec<TypeId>, TypeId),
    // todo could StmtId be replaced with SymbolId (the symbol that defines the function)
    Parameter(StmtId, usize),
    Struct(StmtId),
    // todo could StmtId be replaced with SymbolId (the symbol that defines the struct)
    Field(StmtId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, NativeFnKind),
}
