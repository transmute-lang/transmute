pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod ids;
pub mod literal;
pub mod operators;
pub mod passes;
pub mod statement;

use crate::ast::expression::{Expression, Typed, TypedState, Untyped};
use crate::ast::identifier_ref::{Bound, BoundState, IdentifierRef, Unbound};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::passes::exit_points_resolver::{ExitPoint, ExitPointsResolver};
use crate::ast::passes::implicit_ret_converter::ImplicitRetConverter;
use crate::ast::passes::operators_converter::OperatorsConverter;
use crate::ast::statement::{Statement, StatementKind};
use crate::error::Diagnostics;
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
    statements: VecMap<StmtId, Statement<T, B>>,
    /// Root statements
    root: Vec<StmtId>,
    /// All symbols
    symbols: VecMap<SymbolId, Symbol>,
    /// All types
    types: VecMap<TypeId, Type>,
    state: S,
}

#[derive(Debug, PartialEq)]
pub struct Raw {}

#[derive(Debug, PartialEq)]
pub struct NoOperators {}

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
    pub fn statements(&self) -> &VecMap<StmtId, Statement<T, B>> {
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

impl Ast<Raw, Untyped, Unbound> {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef<Unbound>>,
        expressions: Vec<Expression<Untyped>>,
        statements: Vec<Statement<Untyped, Unbound>>,
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
            state: Raw {},
        }
    }

    pub fn convert_operators(self) -> Ast<NoOperators, Untyped, Unbound> {
        {
            let output = OperatorsConverter::new(self.identifiers, self.identifier_refs)
                .convert(self.expressions);

            Ast::<NoOperators, Untyped, Unbound> {
                identifiers: output.identifiers,
                identifier_refs: output.identifier_refs,
                expressions: output.expressions,
                statements: self.statements,
                root: self.root,
                symbols: self.symbols,
                types: self.types,
                state: NoOperators {},
            }
        }
    }
}

impl Ast<NoOperators, Untyped, Unbound> {
    pub fn convert_implicit_ret(mut self) -> Ast<ExplicitRet, Untyped, Unbound> {
        let converter = ImplicitRetConverter::new();

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
    pub fn resolve_exit_points(self) -> Ast<ExitPoints, Untyped, Unbound> {
        let mut exit_points = HashMap::new();
        let mut unreachable = vec![];

        for (_, stmt) in self.statements.iter() {
            if let &StatementKind::<Untyped, Unbound>::LetFn(_, _, _, expr_id) = stmt.kind() {
                let mut output = ExitPointsResolver::new(&self.expressions, &self.statements)
                    .exit_points(expr_id);
                exit_points.insert(expr_id, output.exit_points);
                unreachable.append(&mut output.unreachable);
            }
        }

        unreachable.sort();
        unreachable.dedup();

        Ast::<ExitPoints, Untyped, Unbound> {
            identifiers: self.identifiers,
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
            statements: self.statements,
            root: self.root,
            symbols: self.symbols,
            types: self.types,
            state: ExitPoints {
                exit_points,
                unreachable,
            },
        }
    }
}

impl Ast<ExitPoints, Untyped, Unbound> {
    pub fn resolve(self, natives: Natives) -> Result<ResolvedAst, Diagnostics> {
        let expressions_count = self.expressions.len();
        let statements_count = self.statements.len();

        Resolver::new(&self.state.exit_points, &self.state.unreachable)
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
                    state: self.state,
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

    pub fn statement(&self, id: StmtId) -> &Statement<Untyped, Unbound> {
        &self.statements[id]
    }
}

impl<R> Ast<R, Typed, Bound> {
    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef<Bound> {
        &self.identifier_refs[id]
    }

    pub fn symbol_by_ident_ref_id(&self, id: IdentRefId) -> &Symbol {
        &self.symbols[self.identifier_refs[id].symbol_id()]
    }

    pub fn expression(&self, id: ExprId) -> &Expression<Typed> {
        &self.expressions[id]
    }

    pub fn expression_type(&self, id: ExprId) -> &Type {
        &self.types[self.expressions[id].type_id()]
    }

    pub fn statement(&self, id: StmtId) -> &Statement<Typed, Bound> {
        &self.statements[id]
    }

    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        &self.symbols[id]
    }

    pub fn ty(&self, id: TypeId) -> &Type {
        &self.types[id]
    }
}
