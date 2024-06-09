pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::{Expression, Typed, TypedState, Untyped};
use crate::ast::identifier_ref::{Bound, BoundState, IdentifierRef, Unbound};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::statement::Statement;
use crate::desugar::ImplicitRetConverter;
use crate::error::Diagnostics;
use crate::exit_points::ExitPoint;
use crate::natives::Natives;
use crate::resolver::{Resolver, Symbol, Type};
use crate::vec_map::VecMap;
use std::collections::HashMap;

pub type ResolvedAst = Ast<ExitPoints, Typed, Bound>;

#[derive(Debug, PartialEq)]
pub struct Ast<S, T, B>
where
    T: TypedState,
    B: BoundState,
{
    /// Unique identifiers names
    identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    identifier_refs: VecMap<IdentRefId, IdentifierRef<B>>,
    /// All expressions
    expressions: VecMap<ExprId, Expression<T>>,
    /// All statements
    statements: VecMap<StmtId, Statement<B>>,
    /// Root statements
    // todo replace with Statements
    root: Vec<StmtId>,
    /// All symbols
    symbols: VecMap<SymbolId, Symbol>,
    /// All types
    types: VecMap<TypeId, Type>,
    state: S,
}

#[derive(Debug, PartialEq)]
pub struct ImplicitRet {}

#[derive(Debug, PartialEq)]
pub struct ExplicitRet {}

#[derive(Debug, PartialEq)]
pub struct ExitPoints {
    exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    unreachable: Vec<ExprId>,
}

impl<S, T, B> Ast<S, T, B>
where
    T: TypedState,
    B: BoundState,
{
    pub fn roots(&self) -> &Vec<StmtId> {
        &self.root
    }

    pub fn identifiers(&self) -> &VecMap<IdentId, String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id]
    }

    pub fn root_statements(&self) -> &Vec<StmtId> {
        &self.root
    }

    #[cfg(test)]
    pub fn identifier_ref_id(&self, start: usize) -> IdentRefId {
        for (id, ident_ref) in &self.identifier_refs {
            if ident_ref.ident().span().start() == start {
                return id;
            }
        }
        panic!("No identifier ref found at {}", start)
    }

    #[cfg(test)]
    pub fn expressions(&self) -> &VecMap<ExprId, Expression<T>> {
        &self.expressions
    }

    #[cfg(test)]
    pub fn statements(&self) -> &VecMap<StmtId, Statement<B>> {
        &self.statements
    }

    #[cfg(test)]
    pub fn expression_id(&self, start: usize) -> ExprId {
        for (id, expr) in &self.expressions {
            if expr.span().start() == start {
                return id;
            }
        }
        panic!("No expression found at {}", start)
    }

    #[cfg(test)]
    pub fn statement_id(&self, start: usize) -> StmtId {
        for (id, stmt) in &self.statements {
            if stmt.span().start() == start {
                return id;
            }
        }
        panic!("No statement found at {}", start)
    }
}

impl Ast<ImplicitRet, Untyped, Unbound> {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef<Unbound>>,
        expressions: Vec<Expression<Untyped>>,
        statements: Vec<Statement<Unbound>>,
        root: Vec<StmtId>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs: identifier_refs.into(),
            expressions: expressions.into(),
            statements: statements.into(),
            root,
            symbols: Default::default(),
            types: Default::default(),
            state: ImplicitRet {},
        }
    }

    pub fn convert_implicit_ret(
        mut self,
        converter: ImplicitRetConverter,
    ) -> Ast<ExplicitRet, Untyped, Unbound> {
        for statement in converter.convert(&self) {
            self.statements.insert(statement.id(), statement);
        }
        Ast::<ExplicitRet, Untyped, Unbound> {
            identifiers: self.identifiers,
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
            statements: self.statements,
            root: self.root,
            symbols: self.symbols,
            types: self.types,
            state: ExplicitRet {},
        }
    }
}

impl Ast<ExplicitRet, Untyped, Unbound> {
    pub fn resolve(self, resolver: Resolver, natives: Natives) -> Result<ResolvedAst, Diagnostics> {
        let expressions_count = self.expressions.len();
        let statements_count = self.statements.len();

        resolver
            .resolve(
                self.identifiers,
                self.identifier_refs,
                self.expressions,
                self.statements,
                self.root,
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

                Ast::<ExitPoints, Typed, Bound> {
                    identifiers: r.identifiers,
                    identifier_refs: r.identifier_refs,
                    expressions: r.expressions,
                    statements: r.statements,
                    root: r.root,
                    symbols: r.symbols,
                    types: r.types,
                    state: ExitPoints {
                        exit_points: r.exit_points,
                        unreachable: r.unreachable,
                    },
                }
            })
    }
}

impl<R> Ast<R, Untyped, Unbound> {
    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Unbound> {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression<Untyped> {
        &self.expressions[id]
    }

    pub fn statement(&self, id: StmtId) -> &Statement<Unbound> {
        &self.statements[id]
    }
}

impl<R> Ast<R, Typed, Bound> {
    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Bound> {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression<Typed> {
        &self.expressions[id]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions[id].ty_id()]
    }

    pub fn statement(&self, id: StmtId) -> &Statement<Bound> {
        &self.statements[id]
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id]
    }

    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id]
    }
}
