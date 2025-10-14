use crate::natives::{Natives, Type};
use crate::nodes::{
    Annotation, ExitPoints, Expression, ExpressionKind, Field, Identifier, IdentifierRef, Literal,
    LiteralKind, Parameter, Return, Statement, TypeDef,
};
use crate::passes::resolver::Resolver;
use crate::symbol::{Symbol, SymbolKind};
use transmute_core::error::Diagnostics;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::vec_map::VecMap;
use transmute_nst::nodes::Expression as NstExpression;
use transmute_nst::nodes::Field as NstField;
use transmute_nst::nodes::Identifier as NstIdentifier;
use transmute_nst::nodes::IdentifierRef as NstIdentifierRef;
use transmute_nst::nodes::Nst;
use transmute_nst::nodes::Parameter as NstParameter;
use transmute_nst::nodes::Return as NstReturn;
use transmute_nst::nodes::Statement as NstStatement;
use transmute_nst::nodes::StatementKind as NstStatementKind;

pub mod hir_print;
pub mod natives;
pub mod nodes;
mod passes;
pub mod symbol;

pub trait Resolve {
    fn resolve(self) -> Result<Hir, Diagnostics<()>>
    where
        Self: Sized,
    {
        self.resolve_with_natives(Natives::default())
    }

    fn resolve_with_natives(self, natives: Natives) -> Result<Hir, Diagnostics<()>>;
}

impl Resolve for Nst {
    fn resolve_with_natives(self, natives: Natives) -> Result<Hir, Diagnostics<()>> {
        Resolver::new().resolve(natives, self)
    }
}

#[derive(Debug, PartialEq)]
pub struct Hir {
    /// Unique identifiers names
    pub identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    /// All expressions
    pub expressions: VecMap<ExprId, Expression>,
    /// All statements
    pub statements: VecMap<StmtId, Statement>,
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

impl Hir {
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

trait IntoBound<T> {
    fn into_bound(self, symbol_id: SymbolId) -> T;
}

impl IntoBound<IdentifierRef> for NstIdentifierRef {
    fn into_bound(self, symbol_id: SymbolId) -> IdentifierRef {
        IdentifierRef {
            id: self.id,
            ident: Identifier {
                id: self.ident.id,
                span: self.ident.span,
                symbol_id,
            },
        }
    }
}

impl IntoBound<Identifier> for NstIdentifier {
    fn into_bound(self, symbol_id: SymbolId) -> Identifier {
        Identifier {
            id: self.id,
            span: self.span,
            symbol_id,
        }
    }
}

trait IntoTyped<T> {
    fn into_typed(self, type_id: TypeId) -> T;
}

impl IntoTyped<Expression> for NstExpression {
    fn into_typed(self, type_id: TypeId) -> Expression {
        Expression {
            id: self.id,
            kind: self.kind,
            span: self.span,
            type_id,
        }
    }
}

impl IntoTyped<Return> for NstReturn {
    fn into_typed(self, type_id: TypeId) -> Return {
        Return {
            type_def_id: self.type_def_id,
            typed_id: type_id,
        }
    }
}

trait IntoBoundTyped<T> {
    fn into_bound_typed(self, symbol_id: SymbolId, type_id: TypeId) -> T;
}

impl IntoBoundTyped<Parameter> for NstParameter {
    fn into_bound_typed(self, symbol_id: SymbolId, type_id: TypeId) -> Parameter {
        Parameter {
            identifier: Identifier {
                id: self.identifier.id,
                span: self.identifier.span,
                symbol_id,
            },
            type_def_id: self.type_def_id,
            span: self.span,
            type_id,
        }
    }
}

impl IntoBoundTyped<Field> for NstField {
    fn into_bound_typed(self, symbol_id: SymbolId, type_id: TypeId) -> Field {
        Field {
            identifier: Identifier {
                id: self.identifier.id,
                span: self.identifier.span,
                symbol_id,
            },
            type_def_id: self.type_def_id,
            span: self.span,
            type_id,
        }
    }
}

trait TryAsLiteral {
    fn try_as_literal(&self) -> Option<&Literal>;
}

impl TryAsLiteral for NstExpression {
    fn try_as_literal(&self) -> Option<&Literal> {
        match &self.kind {
            ExpressionKind::Literal(lit) => Some(lit),
            _ => None,
        }
    }
}

trait As {
    fn as_struct(&self) -> (&NstIdentifier, &Vec<Annotation>, &Vec<NstField>);

    fn as_function(
        &self,
    ) -> (
        &NstIdentifier,
        &Vec<Annotation>,
        &Vec<NstParameter>,
        &ExprId,
    );

    fn as_use(&self) -> &Vec<IdentRefId>;
}

impl As for NstStatement {
    fn as_struct(&self) -> (&NstIdentifier, &Vec<Annotation>, &Vec<NstField>) {
        match &self.kind {
            NstStatementKind::Struct(identifier, annotations, implementation) => {
                (identifier, annotations, implementation)
            }
            _ => panic!("struct expected, got {:?}", self),
        }
    }

    fn as_function(
        &self,
    ) -> (
        &NstIdentifier,
        &Vec<Annotation>,
        &Vec<NstParameter>,
        &ExprId,
    ) {
        match &self.kind {
            NstStatementKind::LetFn(ident, annotations, parameters, _, expression) => {
                (ident, annotations, parameters, expression)
            }
            _ => panic!("function expected, got {:?}", self),
        }
    }

    fn as_use(&self) -> &Vec<IdentRefId> {
        match &self.kind {
            NstStatementKind::Use(idents) => idents,
            _ => panic!("use expected, got {:?}", self),
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
