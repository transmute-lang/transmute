use crate::bound::{Bound, BoundState, Unbound};
use crate::exit_points::ExitPoints;
use crate::expression::Expression;
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::natives::{Natives, Type};
use crate::passes::exit_points_resolver::ExitPointsResolver;
use crate::passes::implicit_ret_converter::ImplicitRetConverter;
use crate::passes::operators_converter::OperatorsConverter;
use crate::passes::resolver::Resolver;
use crate::statement::{Field, Parameter, Return, Statement, TypeDef};
use crate::symbol::Symbol;
use crate::typed::{Typed, TypedState, Untyped};
use std::collections::HashMap;
use transmute_ast::statement::StatementKind as AstStatementKind;
use transmute_ast::Ast;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::vec_map::VecMap;

pub mod bound;
pub mod exit_points;
pub mod expression;
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

pub fn resolve(ast: Ast) -> Result<ResolvedHir, Diagnostics> {
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
    pub roots: Vec<StmtId>,
    /// All symbols
    pub symbols: VecMap<SymbolId, Symbol>,
    /// All types
    pub types: VecMap<TypeId, Type>,
    /// All exit exit points
    pub exit_points: ExitPoints,
}

impl UnresolvedHir {
    pub fn resolve(self, natives: Natives) -> Result<ResolvedHir, Diagnostics> {
        #[cfg(debug_assertions)]
        let (expressions_count, statements_count) = (self.expressions.len(), self.statements.len());

        let resolved_hir = Resolver::new().resolve(natives, self)?;

        #[cfg(debug_assertions)]
        {
            debug_assert!(
                expressions_count == resolved_hir.expressions.len(),
                "expr count don't match ({} != {})",
                expressions_count,
                resolved_hir.expressions.len()
            );

            debug_assert!(
                statements_count == resolved_hir.statements.len(),
                "expr count don't match ({} != {})",
                statements_count,
                resolved_hir.statements.len()
            );
        }

        Ok(resolved_hir)
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

        // convert implicit ret to explicit ret
        let explicit_rets =
            ImplicitRetConverter::new().convert(&ast.roots, ast.statements, expressions);
        let statements = explicit_rets.statements;
        let expressions = explicit_rets.expressions;

        // compute exit points
        let mut exit_points = HashMap::new();
        let mut unreachable = vec![];

        for (_, stmt) in statements.iter() {
            if let &AstStatementKind::LetFn(_, _, _, expr_id) = &stmt.kind {
                let mut output =
                    ExitPointsResolver::new(&expressions, &statements).exit_points(expr_id);

                #[cfg(test)]
                println!("Computed exit points and unreachable for {expr_id:?}: {output:?}");

                exit_points.insert(expr_id, output.exit_points);
                unreachable.append(&mut output.unreachable);
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
            roots: ast.roots,
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
}
