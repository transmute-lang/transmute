use crate::bound::{Bound, BoundState, Unbound};
use crate::exit_points::ExitPoints;
use crate::expression::Expression;
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::natives::{Natives, Type};
use crate::passes::exit_points_resolver::{ExitPointsResolver, Output as ExitPointsResolverOutput};
use crate::passes::implicit_ret_converter::{
    ImplicitRetResolver, Output as ImplicitRetResolverOutput,
};
use crate::passes::operators_converter::OperatorsConverter;
use crate::passes::resolver::Resolver;
use crate::statement::{Field, Parameter, Return, Statement, TypeDef};
use crate::symbol::Symbol;
use crate::typed::{Typed, TypedState, Untyped};
use transmute_ast::statement::StatementKind as AstStatementKind;
use transmute_ast::Ast;
use transmute_core::error::Diagnostics;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::vec_map::VecMap;

pub mod bound;
pub mod exit_points;
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

pub fn resolve(ast: Ast) -> Result<ResolvedHir, Diagnostics<()>> {
    UnresolvedHir::from(ast).resolve(Natives::default())
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

impl From<Ast> for UnresolvedHir {
    fn from(ast: Ast) -> Self {
        // convert operators to function calls
        let operator_free =
            OperatorsConverter::new(ast.identifiers, ast.identifier_refs).convert(ast.expressions);

        let expressions = operator_free.expressions;
        let identifiers = operator_free.identifiers;
        let identifier_refs = operator_free.identifier_refs;

        // convert implicit return statements/expressions to `Ret(..., RetMode::Implicit)`
        // statements
        let ImplicitRetResolverOutput {
            statements,
            expressions,
        } = ImplicitRetResolver::new().resolve(ast.root, ast.statements, expressions);

        // here, we have two kind of `Ret` statements:
        //  - explicit, which are present in the source code (`ret x;`)
        //  - implicit, which are not present in the source code but that happen to be the last
        //    statements on their execution path in their function

        // compute exit points, i.e. Ret statements (explicit or implicit) that are actually
        // reachable. we also compute the set of unreachable expression.
        let mut exit_points = IdMap::new();
        let mut unreachable = Vec::new();

        for (_, stmt) in statements.iter() {
            if let &AstStatementKind::LetFn(_, _, _, _, expr_id) = &stmt.kind {
                let ExitPointsResolverOutput {
                    exit_points: new_exit_points,
                    unreachable: mut new_unreachable,
                } = ExitPointsResolver::new(&expressions, &statements).resolve(expr_id);

                #[cfg(test)]
                println!("{}:{}: Computed exit points={new_exit_points:?} and unreachable={new_unreachable:?} for {expr_id:?}", file!(), line!());

                exit_points.insert(expr_id, new_exit_points);
                unreachable.append(&mut new_unreachable);
            }
        }

        unreachable.sort();
        unreachable.dedup();

        Self {
            identifiers,
            identifier_refs: identifier_refs
                .into_iter()
                .map(|i| (i.0, IdentifierRef::from(i.1)))
                .collect::<VecMap<IdentRefId, IdentifierRef<Unbound>>>(),
            expressions: expressions
                .into_iter()
                .map(|e| (e.0, Expression::from(e.1)))
                .collect::<VecMap<ExprId, Expression<Untyped>>>(),
            statements: statements
                .into_iter()
                .map(|s| (s.0, Statement::from(s.1)))
                .collect::<VecMap<StmtId, Statement<Untyped, Unbound>>>(),
            type_defs: ast
                .type_defs
                .into_iter()
                .map(|e| (e.0, TypeDef::from(e.1)))
                .collect::<VecMap<TypeDefId, TypeDef>>(),
            root: ast.root,
            symbols: Default::default(),
            types: Default::default(),
            exit_points: ExitPoints {
                exit_points,
                unreachable,
            },
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

trait FindSymbol {
    // todo:refactor instead of param_types, pass a RequiredSymbolKind
    /// deprecated: this is quite useless, the caller knows better what it wants to get, and this
    /// function does not crawl any scope up... `find_symbol_id_by_ident_and_param_types` does.
    /// Note that `find_type_id_by_identifier` does crawl the scope stack too, through
    /// `find_symbol_id_by_ident_and_param_types`
    #[deprecated]
    fn find(
        &self,
        all_symbols: &VecMap<SymbolId, Symbol>,
        ident: IdentId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId>;
}
