pub mod bound;
pub mod exit_points;
pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod literal;
pub mod passes;
pub mod statement;
pub mod typed;

use crate::ast::statement::StatementKind;
use crate::ast::Ast;
use crate::error::Diagnostics;
use crate::hir::bound::{Bound, BoundState, Unbound};
use crate::hir::exit_points::ExitPoints;
use crate::hir::expression::Expression;
use crate::hir::identifier_ref::IdentifierRef;
use crate::hir::passes::exit_points_resolver::ExitPointsResolver;
use crate::hir::passes::implicit_ret_converter::ImplicitRetConverter;
use crate::hir::passes::operators_converter::OperatorsConverter;
use crate::hir::passes::resolver::{Resolver, Symbol};
use crate::hir::statement::Statement;
use crate::hir::typed::{Typed, TypedState, Untyped};
use crate::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::natives::Natives;
use crate::vec_map::VecMap;
use std::collections::HashMap;

pub use crate::hir::passes::resolver::SymbolKind;
pub use crate::hir::passes::resolver::Type;

pub type UnresolvedHir = Hir<Untyped, Unbound>;
pub type ResolvedHir = Hir<Typed, Bound>;

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
    /// Root statements
    pub roots: Vec<StmtId>,
    /// All symbols
    pub symbols: VecMap<SymbolId, Symbol>,
    /// All types
    pub types: VecMap<TypeId, Type>,
    /// All exit exit points
    pub exit_points: ExitPoints,
}

impl Hir<Untyped, Unbound> {
    pub fn resolve(self, natives: Natives) -> Result<Hir<Typed, Bound>, Diagnostics> {
        let expressions_count = self.expressions.len();
        let statements_count = self.statements.len();

        Resolver::new(&self.exit_points.exit_points, &self.exit_points.unreachable)
            .resolve(
                self.identifiers,
                self.identifier_refs,
                self.expressions,
                self.statements,
                self.roots,
                natives,
            )
            .map(|r| {
                debug_assert!(
                    expressions_count == r.expressions.len(),
                    "expr count don't match ({} != {})",
                    expressions_count,
                    r.expressions.len()
                );
                debug_assert!(
                    statements_count == r.statements.len(),
                    "stmt count don't match ({} != {})",
                    statements_count,
                    r.statements.len()
                );

                Hir::<Typed, Bound> {
                    identifiers: r.identifiers,
                    identifier_refs: r.identifier_refs,
                    expressions: r.expressions,
                    statements: r.statements,
                    roots: r.root,
                    symbols: r.symbols,
                    types: r.types,
                    exit_points: self.exit_points,
                }
            })
    }
}

impl From<Ast> for Hir<Untyped, Unbound> {
    fn from(mut ast: Ast) -> Self {
        // convert operators to function calls
        let operator_free =
            OperatorsConverter::new(ast.identifiers, ast.identifier_refs).convert(ast.expressions);

        // convert implicit ret to explicit ret
        for new_statement in ImplicitRetConverter::new().convert(
            &ast.roots,
            &ast.statements,
            &operator_free.expressions,
        ) {
            ast.statements.insert(new_statement.id(), new_statement);
        }

        // compute exit points
        let mut exit_points = HashMap::new();
        let mut unreachable = vec![];

        for (_, stmt) in ast.statements.iter() {
            if let &StatementKind::LetFn(_, _, _, expr_id) = stmt.kind() {
                let mut output =
                    ExitPointsResolver::new(&operator_free.expressions, &ast.statements)
                        .exit_points(expr_id);
                exit_points.insert(expr_id, output.exit_points);
                unreachable.append(&mut output.unreachable);
            }
        }

        unreachable.sort();
        unreachable.dedup();

        Self {
            identifiers: operator_free.identifiers,
            identifier_refs: operator_free
                .identifier_refs
                .into_iter()
                .map(|i| (i.0, crate::hir::identifier_ref::IdentifierRef::from(i.1)))
                .collect::<VecMap<IdentRefId, IdentifierRef<Unbound>>>(),
            expressions: operator_free
                .expressions
                .into_iter()
                .map(|e| (e.0, crate::hir::expression::Expression::from(e.1)))
                .collect::<VecMap<ExprId, Expression<Untyped>>>(),
            statements: ast
                .statements
                .into_iter()
                .map(|s| (s.0, crate::hir::statement::Statement::from(s.1)))
                .collect::<VecMap<StmtId, Statement<Untyped, Unbound>>>(),
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

impl Hir<Typed, Bound> {
    pub fn symbol_by_ident_ref_id(&self, id: IdentRefId) -> &Symbol {
        &self.symbols[self.identifier_refs[id].symbol_id()]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions[id].type_id()]
    }
}
