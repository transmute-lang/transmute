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
            SymbolKind::LetFn(_, _, params, ret_type_id) => (params, *ret_type_id),
            _ => panic!("{:?} is not a function", self),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    NotFound,
    Let(IdentId, StmtId),
    LetFn(IdentId, StmtId, Vec<TypeId>, TypeId),
    // todo:refactoring could StmtId be replaced with SymbolId (the symbol that defines the function)
    Parameter(IdentId, StmtId, usize),
    Struct(IdentId, StmtId),
    // todo:refactoring could StmtId be replaced with SymbolId (the symbol that defines the struct)
    Field(IdentId, StmtId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, NativeFnKind),
}
