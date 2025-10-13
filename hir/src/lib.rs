use crate::bound::{Bound, BoundState, Unbound};
use crate::expression::{Expression};
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::natives::{Natives, Type};
use crate::passes::resolver::Resolver;
use crate::statement::{Field, Parameter, Return, Statement, TypeDef};
use crate::symbol::{Symbol, SymbolKind};
use crate::typed::{Typed, TypedState, Untyped};
use transmute_core::error::Diagnostics;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::vec_map::VecMap;
use transmute_nst::nodes::Nst;
pub use transmute_nst::nodes::{ExitPoint, ExitPoints};

pub mod bound;
pub mod expression;
pub mod hir_print;
pub mod identifier;
pub mod identifier_ref;
pub mod literal;
pub mod natives;
pub mod passes;
pub mod statement;
pub mod symbol;
pub mod typed;

pub type UnresolvedHir = Hir<Untyped, Unbound>;
pub type ResolvedHir = Hir<Typed, Bound>;

pub type ResolvedExpression = Expression<Typed>;
pub type ResolvedStatement = Statement<Typed, Bound>;
pub type ResolvedIdentifier = Identifier<Bound>;
pub type ResolvedIdentifierRef = IdentifierRef<Bound>;
pub type ResolvedParameter = Parameter<Typed, Bound>;
pub type ResolvedReturn = Return<Typed>;
pub type ResolvedField = Field<Typed, Bound>;

pub fn resolve(nst: Nst) -> Result<ResolvedHir, Diagnostics<()>> {
    UnresolvedHir::from(nst).resolve(Natives::default())
}

#[derive(Debug, PartialEq)]
pub struct Hir<T, B>
where
    T: TypedState,
    B: BoundState,
{
    /// Unique identifiers names
    pub identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef<B>>,
    /// All expressions
    pub expressions: VecMap<ExprId, Expression<T>>,
    /// All statements
    pub statements: VecMap<StmtId, Statement<T, B>>,
    /// Types
    pub type_defs: VecMap<TypeDefId, TypeDef>,
    /// Root statements
    pub root: StmtId,
    /// All symbols
    pub symbols: VecMap<SymbolId, Symbol>,
    /// All types
    pub types: VecMap<TypeId, Type>,
    /// All exit points
    pub exit_points: ExitPoints,
}

impl UnresolvedHir {
    pub fn resolve(self, natives: Natives) -> Result<ResolvedHir, Diagnostics<()>> {
        Resolver::new().resolve(natives, self)
    }
}

impl From<Nst> for UnresolvedHir {
    fn from(nst: Nst) -> Self {
        Self {
            identifiers: nst.identifiers,
            identifier_refs: nst
                .identifier_refs
                .into_iter()
                .map(|i| (i.0, IdentifierRef::from(i.1)))
                .collect::<VecMap<IdentRefId, IdentifierRef<Unbound>>>(),
            expressions: nst
                .expressions
                .into_iter()
                .map(|e| (e.0, Expression::from(e.1)))
                .collect::<VecMap<ExprId, Expression<Untyped>>>(),
            statements: nst
                .statements
                .into_iter()
                .map(|s| (s.0, Statement::from(s.1)))
                .collect::<VecMap<StmtId, Statement<Untyped, Unbound>>>(),
            type_defs: nst
                .type_defs
                .into_iter()
                .map(|e| (e.0, TypeDef::from(e.1)))
                .collect::<VecMap<TypeDefId, TypeDef>>(),
            root: nst.root,
            symbols: Default::default(),
            types: Default::default(),
            exit_points: nst.exit_points,
        }
    }
}

impl ResolvedHir {
    pub fn symbol_by_ident_ref_id(&self, id: IdentRefId) -> &Symbol {
        &self.symbols[self.identifier_refs[id].resolved_symbol_id()]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions[id].resolved_type_id()]
    }

    pub fn void_type_id(&self) -> TypeId {
        self.types
            .iter()
            .find(|(_, t)| matches!(t, Type::Void))
            .unwrap()
            .0
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
enum RequiredSymbolKind<'a> {
    Function(&'a [TypeId]),
    Other,
}

impl RequiredSymbolKind<'_> {
    pub fn matches(&self, symbol_kind: &SymbolKind) -> bool {
        match self {
            RequiredSymbolKind::Function(required_parameter_types) => match symbol_kind {
                SymbolKind::LetFn(_, _, parameter_types, _)
                | SymbolKind::Native(_, parameter_types, ..) => {
                    *required_parameter_types == parameter_types.as_slice()
                }
                _ => false,
            },
            RequiredSymbolKind::Other => {
                !(matches!(symbol_kind, SymbolKind::LetFn(..))
                    || matches!(symbol_kind, SymbolKind::Native(..)))
            }
        }
    }
}

trait FindSymbol {
    fn find(
        &self,
        all_symbols: &VecMap<SymbolId, Symbol>,
        ident: IdentId,
        kind: RequiredSymbolKind,
    ) -> Option<SymbolId>;
}

impl FindSymbol for IdMap<IdentId, Vec<SymbolId>> {
    fn find(
        &self,
        all_symbols: &VecMap<SymbolId, Symbol>,
        ident: IdentId,
        kind: RequiredSymbolKind,
    ) -> Option<SymbolId> {
        self.get(&ident).and_then(|symbols| {
            symbols
                .iter()
                .rev()
                .find(|s| kind.matches(&all_symbols[**s].kind))
                .copied()
        })
    }
}
