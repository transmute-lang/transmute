use crate::natives::{NativeFnKind, Type};
use transmute_core::id_map::IdMap;
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

    pub fn as_annotation(&self) -> &IdentId {
        match &self.kind {
            SymbolKind::Annotation(ident, _) => ident,
            _ => panic!("{:?} is not an annotation", self),
        }
    }

    pub(crate) fn as_namespace_mut(&mut self) -> &mut IdMap<IdentId, Vec<SymbolId>> {
        if !matches!(self.kind, SymbolKind::Namespace(..)) {
            panic!("{:?} is not a namespace", self);
        }
        match &mut self.kind {
            SymbolKind::Namespace(_, symbols) => symbols,
            _ => unreachable!(),
        }
    }

    pub fn as_namespace(&self) -> &IdMap<IdentId, Vec<SymbolId>> {
        match &self.kind {
            SymbolKind::Namespace(_, symbols) => symbols,
            _ => panic!("{:?} is not a namespace", self),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    NotFound,
    Let(IdentId, StmtId),
    // todo:refactoring would it help that the function symbol only points to a StmtId, as for
    //  structs for instance? this may allow to implement insert_function as we do for insert_struct
    //  but what would be the drawbacks? when searching for a symbol with
    //  find_symbol_id_by_ident_and_param_types we would need to dereference the SymbolId to match
    //  on types... this would allow clones and duplicated `Vec`s (in `SymbolKind` and `LetFn`).
    LetFn(IdentId, StmtId, Vec<TypeId>, TypeId),
    // todo:refactoring could StmtId be replaced with SymbolId (the symbol that defines the function)
    Parameter(IdentId, StmtId, usize),
    Struct(IdentId, StmtId),
    Annotation(IdentId, StmtId),
    // todo:refactoring could StmtId be replaced with SymbolId (the symbol that defines the struct)
    Field(IdentId, StmtId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, NativeFnKind),
    Namespace(
        /// namespace's identifier, if not root
        IdentId,
        /// namespace's content
        // todo:
        //  - should it be a Scope?; or
        //  - should Scope disappear and become a HashMap<>?; or
        //  - should we instead have type Scope = HashMap<>?
        //  at least it should be something that makes insert(IdentId, SymbolId) easy to perform
        IdMap<IdentId, Vec<SymbolId>>,
    ),
}
