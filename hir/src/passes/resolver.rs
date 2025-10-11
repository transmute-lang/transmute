use crate::bound::{Bound, BoundMultiple, Unbound};
use crate::expression::{ExpressionKind, Target};
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::literal::{Literal, LiteralKind};
use crate::natives::{Native, Natives, Type};
use crate::statement::{
    Annotation, Field, Implementation, Parameter, RetMode, Return, Statement, StatementKind,
    TypeDefKind,
};
use crate::symbol::{Symbol, SymbolKind};
use crate::typed::{Typed, Untyped};
use crate::{
    FindSymbol, RequiredSymbolKind, ResolvedExpression, ResolvedHir, ResolvedStatement,
    UnresolvedHir,
};
use bimap::BiHashMap;
use std::any::Any;
use std::collections::HashMap;
use std::{mem, vec};
use transmute_core::error::Diagnostics;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::span::Span;
use transmute_core::stack::Iter;
use transmute_core::stack::Stack;
use transmute_core::vec_map::VecMap;
use transmute_nst::nodes::ExitPoint;

static NATIVE_ANNOTATION: [&str; 2] = ["std", "native"];

type Function<T, B> = (
    Identifier<B>,
    Vec<Parameter<T, B>>,
    Return<T>,
    Implementation<ExprId>,
);

// todo:refactoring each `resolve_` method does the actual resolution instead of giving to its
//  caller the information required to resolve

// fixme:feature: compiling the following results in a seg faut when executing:
//   use std.numbers.print;
//   let add(a: number, b: number): number { a + b; }
//   let main(){ print(1+1); }
//  probably due to the redefinition of add, resulting in a recursive mess

// fixme the following requires an import of std.numbers.print, which prevents to name the function
//  'p' as 'print': struct S { s: number } let p(s: S) { s.field.print(); }

pub struct Resolver {
    // out
    identifiers: BiHashMap<IdentId, String>,
    identifier_refs: VecMap<IdentRefId, IdentifierRef<BoundMultiple>>,
    expressions: VecMap<ExprId, ResolvedExpression>,
    statements: VecMap<StmtId, ResolvedStatement>,
    types: BiHashMap<TypeId, Type>,
    types_by_name: HashMap<&'static str, TypeId>,
    symbols: VecMap<SymbolId, Symbol>,
    not_found_symbol_id: SymbolId,

    // work
    namespaces: Stack<SymbolId>,
    scopes: Scopes,
    current_fn: Stack<StmtId>,

    /// maps functions (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    function_symbols: HashMap<StmtId, SymbolId>,
    /// maps structs (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    struct_symbols: HashMap<StmtId, SymbolId>,
    /// maps annotations (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    annotation_symbols: HashMap<StmtId, SymbolId>,
    /// maps parameters and struct fields (by their (`StmtId`, `index`)) to the corresponding symbol
    /// (by their `SymbolId`)
    stmt_symbols: HashMap<(StmtId, usize), SymbolId>,
    /// maps namespaces (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    namespace_symbols: HashMap<StmtId, SymbolId>,
    /// maps `TypeId`s to functions
    type_functions: HashMap<TypeId, HashMap<IdentId, SymbolId>>,

    diagnostics: Diagnostics<()>,
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            identifiers: Default::default(),
            identifier_refs: Default::default(),
            expressions: Default::default(),
            statements: Default::default(),
            types: Default::default(),
            types_by_name: Default::default(),
            symbols: Default::default(),
            not_found_symbol_id: Default::default(),

            namespaces: Default::default(),
            scopes: Default::default(),
            current_fn: Default::default(),

            function_symbols: Default::default(),
            struct_symbols: Default::default(),
            annotation_symbols: Default::default(),
            stmt_symbols: Default::default(),
            namespace_symbols: Default::default(),
            type_functions: Default::default(),

            diagnostics: Default::default(),
        }
    }

    pub fn resolve(
        mut self,
        natives: Natives,
        mut hir: UnresolvedHir,
    ) -> Result<ResolvedHir, Diagnostics<()>> {
        let root = hir.root;

        // init. identifiers
        self.identifiers = BiHashMap::from_iter(mem::take(&mut hir.identifiers));

        for native_name in natives.names().into_iter() {
            // just append all native names, if they are missing
            if !self.identifiers.contains_right(native_name) {
                self.identifiers.insert(
                    IdentId::from(self.identifiers.len()),
                    native_name.to_string(),
                );
            }
        }

        #[cfg(test)]
        {
            let mut ident_ids = self.identifiers.left_values().collect::<Vec<_>>();
            ident_ids.sort();
            for ident_id in ident_ids {
                let name = self.identifiers.get_by_left(ident_id).unwrap();
                println!("{}:{}: {:?} -> {}", file!(), line!(), ident_id, name);
            }
        }

        // init. identifier_refs
        self.identifier_refs.resize(hir.identifier_refs.len());
        #[cfg(debug_assertions)]
        let ident_ref_count = hir.identifier_refs.len();

        // init. expressions
        self.expressions.resize(hir.expressions.len());
        #[cfg(debug_assertions)]
        let expr_count = hir.expressions.len();

        // init. statements
        self.statements.resize(hir.statements.len());
        #[cfg(debug_assertions)]
        let stmt_count = hir.statements.len();

        // init. types
        debug_assert!(hir.types.is_empty());
        let invalid_type_id = TypeId::from(self.types.len());
        self.types.insert(invalid_type_id, Type::Invalid);
        debug_assert_eq!(invalid_type_id, TypeId::from(0));

        let void_type_id = TypeId::from(self.types.len());
        self.types.insert(void_type_id, Type::Void);

        let none_type_id = TypeId::from(self.types.len());
        self.types.insert(none_type_id, Type::None);

        let boolean_type_id = TypeId::from(self.types.len());
        self.types.insert(boolean_type_id, Type::Boolean);

        let number_type_id = TypeId::from(self.types.len());
        self.types.insert(number_type_id, Type::Number);

        let type_type_id = TypeId::from(self.types.len());
        self.types.insert(type_type_id, Type::Type);

        // init. symbols
        self.not_found_symbol_id = self.symbols.create();
        debug_assert_eq!(self.not_found_symbol_id, SymbolId::from(0));
        self.symbols.insert(
            self.not_found_symbol_id,
            Symbol {
                id: self.not_found_symbol_id,
                kind: SymbolKind::NotFound,
                type_id: invalid_type_id,
            },
        );

        // The general resolution idea is as follows (denoted 'STEP n' below):
        //  1. we create symbols for namespaces, annotations and structs that are not contained
        //     within functions (these symbols don't need to lookup / resolve types) to be inserted
        //     in the symbols table
        //  2. we create symbols for `core` namespace
        //  3. we build the root scope as:
        //       a. all symbols from 'core'
        //       b. all root namespaces
        //  4. we create symbols for functions that are not contained within function. They need to
        //     lookup types produced in the first step in order to be inserted in the symbols table
        //  5. we add all function from root namespace to the root scope
        //  6. we resolve all statements, which means (in order where we discover the statements -
        //     by walking the ast top to bottom):
        //       - we resolve the types of structs fields
        //       - we insert symbols for nested functions and structs
        //       - we resolve the type of all expressions contained in functions
        //
        // NOTE: the above means that unless shadowed, symbols from the root namespace (i.e. 'core'
        // and 'std' and any other defined outside any namespace) as well as all symbols from 'core'
        // will be visible from everywhere

        // STEP 1 ----------------------------------------------------------------------------------
        self.scopes.push();
        let root_root_namespace_symbol_id = self.insert_namespace(&hir, root);
        self.namespaces.push(root_root_namespace_symbol_id);
        debug_assert_eq!(self.namespaces.len(), 1, "{:?}", &self.namespaces);

        // STEP 2 ----------------------------------------------------------------------------------
        let core_namespace_ident_id = *self.identifiers.get_by_right("core").unwrap();
        let core_namespace_symbol_id = self.symbols[*self.namespaces.root().unwrap()]
            .as_namespace()
            .get(&core_namespace_ident_id)
            .unwrap()
            .iter()
            .filter_map(|symbols_id| self.symbols.get(*symbols_id))
            .filter_map(|s| match &s.kind {
                SymbolKind::Namespace(ident_id, ..) if ident_id == &core_namespace_ident_id => {
                    Some(s.id)
                }
                _ => None,
            })
            .next()
            .expect("core namespace exists");

        debug_assert_eq!(self.namespaces.len(), 1, "{:?}", &self.namespaces);
        for native in natives.into_iter() {
            let (ident, symbol_id) = match native {
                Native::Fn(native) => {
                    let ident = self.find_ident_id_by_str(native.name);
                    let parameters = native
                        .kind
                        .signature()
                        .0
                        .iter()
                        .map(|t| self.find_type_id_by_type(t))
                        .collect::<Vec<TypeId>>();
                    let ret_type = self.find_type_id_by_type(&native.kind.signature().1);
                    let fn_type_id = self.insert_type(Type::Function(parameters.clone(), ret_type));

                    (
                        ident,
                        self.insert_symbol(
                            ident,
                            SymbolKind::Native(ident, parameters, ret_type, native.kind),
                            fn_type_id,
                        ),
                    )
                }
                Native::Type(native) => {
                    let id = self.find_ident_id_by_str(native.name);
                    (
                        id,
                        self.insert_symbol(
                            id,
                            SymbolKind::NativeType(id, native.ty.clone()),
                            self.find_type_id_by_type(&Type::None),
                        ),
                    )
                }
            };

            self.symbols[core_namespace_symbol_id]
                .as_namespace_mut()
                .entry(ident)
                .or_default()
                .push(symbol_id);
        }
        debug_assert_eq!(self.namespaces.len(), 1, "{:?}", &self.namespaces);

        // we discard all inserted symbols, they are not part of any scope, but only of the 'core'
        // root package
        debug_assert_eq!(self.scopes.len(), 1);
        self.scopes.clear_last();

        // STEP 3.a --------------------------------------------------------------------------------
        // todo:feature replace this with prelude 'use'
        // insert 'core' namespace symbols into the first scope

        self.bring_namespace_symbols_into_scope(core_namespace_symbol_id);

        // STEP 3.b --------------------------------------------------------------------------------
        // insert root namespace's symbols into the first scope
        self.bring_namespace_symbols_into_scope(root_root_namespace_symbol_id);

        // STEP 4 ----------------------------------------------------------------------------------
        debug_assert_eq!(self.scopes.len(), 1, "{:?}", self.namespaces);
        self.insert_namespace_functions(&mut hir, root);
        debug_assert_eq!(self.scopes.len(), 1, "{:?}", self.namespaces);

        // STEP 5 ----------------------------------------------------------------------------------
        // insert root namespace's fn symbols into the first scope
        // todo:refactoring try to use bring_namespace_symbols_into_scope
        let root_scope = self.scopes.last_symbols_mut().unwrap();
        let root_symbols = self.symbols[*self.namespaces.root().unwrap()].as_namespace();
        for ident_id in root_symbols.keys() {
            for symbol_id in root_symbols.get(ident_id).unwrap() {
                if matches!(self.symbols[*symbol_id].kind, SymbolKind::LetFn(..)) {
                    root_scope.entry(*ident_id).or_default().push(*symbol_id);
                }
            }
        }

        // STEP 6 ----------------------------------------------------------------------------------
        debug_assert_eq!(self.namespaces.len(), 1, "{:?}", self.namespaces);
        let root_namespace = hir.statements.remove(root).unwrap();
        self.resolve_statement(&mut hir, root_namespace);
        debug_assert_eq!(self.namespaces.len(), 1, "{:?}", self.namespaces);

        if !self.diagnostics.is_empty() {
            return Err(self.diagnostics);
        }

        let types = VecMap::from_iter(self.types);

        #[cfg(debug_assertions)]
        {
            debug_assert!(
                !self.identifier_refs.has_holes(),
                "identifier_refs has holes. missing: {:?}",
                hir.identifier_refs
            );
            debug_assert!(
                !self.expressions.has_holes(),
                "expressions has holes. missing: {:?}",
                hir.expressions
            );
            debug_assert!(
                !self.statements.has_holes(),
                "statements has holes. missing: {:?}",
                hir.statements
            );
            debug_assert!(
                !self.symbols.has_holes(),
                "symbols has holes: {:?}",
                self.symbols
            );
            debug_assert!(
                !types.has_holes(),
                "types has holes. missing: {:?}",
                hir.types
            );
            debug_assert!(
                hir.identifier_refs.is_empty(),
                "identifier_refs is not empty"
            );
            debug_assert!(
                ident_ref_count <= self.identifier_refs.len(),
                "ident_ref count does not match"
            );
            debug_assert!(hir.expressions.is_empty(), "expressions is not empty");
            debug_assert!(hir.statements.is_empty(), "statements is not empty");
            debug_assert!(
                expr_count == self.expressions.len(),
                "expr count does not match"
            );
            debug_assert!(
                stmt_count == self.statements.len(),
                "stmt count does not match"
            );
        }

        let stmts_ident_ref_ids = self
            .statements
            .iter()
            .flat_map(|(_, stmt)| stmt.collect_ident_ref_ids())
            .collect::<Vec<_>>();

        // here we test all statements that require unique binding for IndentRefs have unique
        // bindings
        #[cfg(debug_assertions)]
        for ident_ref_id in stmts_ident_ref_ids.iter() {
            debug_assert_eq!(
                self.identifier_refs[*ident_ref_id]
                    .resolved_symbol_ids()
                    .len(),
                1
            );
        }

        let expr_ident_ref_ids = self
            .expressions
            .iter()
            .flat_map(|(_, expr)| expr.collect_ident_ref_ids())
            .collect::<Vec<_>>();

        // here we test all expressions that require unique binding for IndentRefs have unique
        // bindings
        #[cfg(debug_assertions)]
        for ident_ref_id in expr_ident_ref_ids.iter() {
            debug_assert_eq!(
                self.identifier_refs[*ident_ref_id]
                    .resolved_symbol_ids()
                    .len(),
                1
            );
        }

        let type_defs_ref_ids = hir
            .type_defs
            .iter()
            .flat_map(|(_, td)| td.collect_ident_ref_ids())
            .collect::<Vec<_>>();

        // here we test all type defs that require unique binding for IndentRefs have unique
        // bindings
        #[cfg(debug_assertions)]
        for ident_ref_id in type_defs_ref_ids.iter() {
            debug_assert_eq!(
                self.identifier_refs[*ident_ref_id]
                    .resolved_symbol_ids()
                    .len(),
                1
            );
        }

        let mut ident_refs = self.identifier_refs;

        // todo:test try to find a way to keep all the statements, including the
        //  `StatementKind::Use` ones, as well as all the related ident_refs (that may have more
        //  than one binding) for the test / dump during tests
        let use_stmts = self
            .statements
            .iter()
            .filter(|(_, stmt)| matches!(stmt.kind, StatementKind::Use(..)))
            .map(|(id, _)| id)
            .collect::<Vec<_>>();

        Ok(ResolvedHir {
            identifiers: VecMap::from_iter(self.identifiers),
            // now, we uniquely bind all collected IdentifierRefs
            identifier_refs: stmts_ident_ref_ids
                .into_iter()
                .chain(expr_ident_ref_ids)
                .chain(type_defs_ref_ids)
                .map(|id| (id, ident_refs.remove(id).unwrap().into_bound_unique()))
                .collect::<VecMap<_, _>>(),
            // we remove all references to Use statements
            expressions: self
                .expressions
                .into_iter()
                .map(|(id, mut expr)| match expr.kind {
                    ExpressionKind::Block(ref mut stmts) => {
                        stmts.retain(|stmt_id| !use_stmts.contains(stmt_id));
                        (id, expr)
                    }
                    _ => (id, expr),
                })
                .collect(),
            // we remove all Use statements and references to Use statements
            statements: self
                .statements
                .into_iter()
                .filter_map(|(id, mut stmt)| match stmt.kind {
                    StatementKind::Use(_) => None,
                    StatementKind::Namespace(_, _, ref mut stmts) => {
                        stmts.retain(|stmt_id| !use_stmts.contains(stmt_id));
                        Some((id, stmt))
                    }
                    _ => Some((id, stmt)),
                })
                .collect(),
            type_defs: hir.type_defs,
            root: hir.root,
            symbols: self.symbols,
            types,
            exit_points: hir.exit_points,
        })
    }

    fn resolve_expression(
        &mut self,
        hir: &mut UnresolvedHir,
        expr_id: ExprId,
    ) -> (TypeId, Option<SymbolId>) {
        if let Some(expr) = self.expressions.get(expr_id) {
            return (
                expr.resolved_type_id(),
                expr.symbol_id(&self.identifier_refs),
            );
        }

        let expr = hir
            .expressions
            .remove(expr_id)
            .expect("expr is not resolved");

        let (type_id, symbol_id) = match &expr.kind {
            ExpressionKind::Assignment(Target::Direct(ident_ref), expr) => {
                (self.resolve_direct_assignment(hir, *ident_ref, *expr), None)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                self.resolve_indirect_assignment(hir, lhs_expr_id, rhs_expr_id)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => (
                self.resolve_if(hir, *cond, *true_branch, *false_branch),
                None,
            ),
            ExpressionKind::Literal(literal) => match literal.kind {
                LiteralKind::Boolean(_) => (self.find_type_id_by_type(&Type::Boolean), None),
                LiteralKind::Number(_) => (self.find_type_id_by_type(&Type::Number), None),
                LiteralKind::String(_) => (
                    self.find_type_id_by_name("std.str.string")
                        .expect("std.str.string exists"),
                    None,
                ),
                LiteralKind::Identifier(ident_ref) => {
                    let symbol_ids =
                        self.resolve_ident_ref(hir, ident_ref, RequiredSymbolKind::Other);
                    debug_assert!(symbol_ids.len() <= 1);
                    let type_id = symbol_ids
                        .first()
                        .map(|s| self.symbols[*s].type_id)
                        .unwrap_or(self.find_type_id_by_type(&Type::Invalid));

                    (type_id, symbol_ids.first().cloned())
                }
            },
            ExpressionKind::Access(expr_id, ident_ref_id) => self.resolve_access(
                hir,
                &expr.span,
                *expr_id,
                *ident_ref_id,
                RequiredSymbolKind::Other,
            ),
            ExpressionKind::FunctionCall(expr_id, params) => (
                self.resolve_function_call(hir, *expr_id, params.clone().as_slice()),
                None,
            ),
            ExpressionKind::While(cond, expr) => self.resolve_while(hir, *cond, *expr),
            ExpressionKind::Block(stmts) => (self.resolve_block(hir, &stmts.clone()), None),
            ExpressionKind::StructInstantiation(ident_ref_id, type_parameters, fields) => (
                self.resolve_struct_instantiation(
                    hir,
                    *ident_ref_id,
                    type_parameters,
                    fields,
                    &expr.span,
                ),
                None,
            ),
            ExpressionKind::ArrayInstantiation(values) => {
                (self.resolve_array_instantiation(hir, values), None)
            }
            ExpressionKind::ArrayAccess(expr, index) => {
                (self.resolve_array_access(hir, *expr, *index), None)
            }
        };

        self.expressions.insert(expr_id, expr.typed(type_id));

        (type_id, symbol_id)
    }

    fn resolve_direct_assignment(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref: IdentRefId,
        expr: ExprId,
    ) -> TypeId {
        // If we have the following:
        //   let add(a: number, b: number): number = {}
        //   let add(a: boolean, b: boolean): boolean = {}
        //
        // then:
        //   add = |a: boolean, b: boolean|: boolean {}
        //
        // must update the value of the 2nd add. Hence, we need to first compute the type
        // of the expression, then find all the symbols matching the name and update the
        // one with the correct function type, i.e. parameter types + return type. This,
        // even though the return type does *not* count in method signature when computing
        // their uniqueness, i.e. x(a: number): number is considered the same as
        // x(a: number): boolean.
        //
        // Similarly:
        //   let add_bool: |boolean, boolean|: boolean = add;
        //
        // chooses the 2nd function as this is the one for which the type matches.
        //
        // todo:feature:fn-value implement the above...

        let rhs_type_id = self.resolve_expression(hir, expr).0;

        // todo:feature:fn-value to search for method, we need to extract the parameter types from the
        //  expr_type, if it corresponds to a function type. We don't have this
        //  information yet and thus we cannot assign to a variable holding a function
        //  (yet).
        let lhs_symbol_ids = self.resolve_ident_ref(hir, ident_ref, RequiredSymbolKind::Other);
        debug_assert!(lhs_symbol_ids.len() <= 1);
        let lhs_type_id = lhs_symbol_ids
            .first()
            .map(|s| self.symbols[*s].type_id)
            .unwrap_or(self.find_type_id_by_type(&Type::Invalid));

        if lhs_type_id == self.find_type_id_by_type(&Type::Invalid) {
            return lhs_type_id;
        }

        if rhs_type_id == self.find_type_id_by_type(&Type::Invalid) {
            return rhs_type_id;
        }

        if rhs_type_id != lhs_type_id {
            self.diagnostics.report_err(
                format!(
                    "RHS expected to be of type {}, got {}",
                    self.find_type_by_type_id(lhs_type_id),
                    self.find_type_by_type_id(rhs_type_id)
                ),
                self.expressions[expr].span.clone(),
                (file!(), line!()),
            );
            return self.find_type_id_by_type(&Type::Invalid);
        }

        rhs_type_id
    }

    fn resolve_indirect_assignment(
        &mut self,
        hir: &mut UnresolvedHir,
        lhs_expr_id: &ExprId,
        rhs_expr_id: &ExprId,
    ) -> (TypeId, Option<SymbolId>) {
        let lhs_type_id = self.resolve_expression(hir, *lhs_expr_id).0;
        let rhs_type_id = self.resolve_expression(hir, *rhs_expr_id).0;
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        if lhs_type_id == invalid_type_id || rhs_type_id == invalid_type_id {
            return (invalid_type_id, None);
        }

        if lhs_type_id != rhs_type_id {
            self.diagnostics.report_err(
                format!(
                    "RHS expected to be of type {}, got {}",
                    self.find_type_by_type_id(lhs_type_id),
                    self.find_type_by_type_id(rhs_type_id)
                ),
                self.expressions[*rhs_expr_id].span.clone(),
                (file!(), line!()),
            );
            return (invalid_type_id, None);
        }

        (lhs_type_id, None)
    }

    fn resolve_if(
        &mut self,
        hir: &mut UnresolvedHir,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> TypeId {
        let cond_type = self.resolve_expression(hir, cond).0;
        let boolean_type_id = self.find_type_id_by_type(&Type::Boolean);
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        if cond_type != boolean_type_id && cond_type != invalid_type_id {
            self.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    self.find_type_by_type_id(cond_type)
                ),
                self.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        let true_branch_type_id = self.resolve_expression(hir, true_branch).0;
        let false_branch_type_id = match false_branch {
            None => self.find_type_id_by_type(&Type::Void),
            Some(e) => self.resolve_expression(hir, e).0,
        };

        let true_branch_type = self.find_type_by_type_id(true_branch_type_id);
        let false_branch_type = self.find_type_by_type_id(false_branch_type_id);

        match (true_branch_type, false_branch_type) {
            (Type::Invalid, _) | (_, Type::Invalid) => invalid_type_id,
            (Type::None, Type::None) => true_branch_type_id,
            // todo:test the following case is not well tested + implement proper error handing
            (Type::None, t) | (t, Type::None) => self.find_type_id_by_type(t),
            (_, Type::Void) | (Type::Void, _) => {
                // todo:feature ifs with only one branch should return option<t>
                self.find_type_id_by_type(&Type::Void)
            }
            (tt, ft) if tt == ft => true_branch_type_id,
            (tt, ft) => {
                let false_branch = &self.expressions[false_branch.expect("false branch exists")];
                self.diagnostics.report_err(
                    format!("Expected type {tt}, got {ft}"),
                    false_branch.span.clone(),
                    (file!(), line!()),
                );
                invalid_type_id
            }
        }
    }

    /// Resolves an identifier ref by its `IdentRefId` and returns the corresponding `SymbolId`.
    /// The resolution starts in the current scope and crawls the scopes stack up until the
    /// identifier is found.
    fn resolve_ident_ref(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref_id: IdentRefId,
        kind: RequiredSymbolKind,
    ) -> Vec<SymbolId> {
        if let Some(ident_ref) = &self.identifier_refs.get(ident_ref_id) {
            return ident_ref.resolved_symbol_ids().to_vec();
        }

        let ident_ref = hir
            .identifier_refs
            .remove(ident_ref_id)
            .expect("ident_ref is not resolved");

        let ident_id = ident_ref.ident.id;

        match self.find_symbol_id_by_ident_and_kind(ident_id, kind) {
            Some(s) => {
                let ident_id = ident_ref.id;
                self.identifier_refs.insert(ident_id, ident_ref.resolved(s));
                self.identifier_refs[ident_id]
                    .resolved_symbol_ids()
                    .to_vec()
            }
            None => {
                // todo:feature propose known alternatives
                match kind {
                    RequiredSymbolKind::Function(param_types) => {
                        self.diagnostics.report_err(
                            format!(
                                "No function '{}' found for parameters of types ({})",
                                self.identifiers.get_by_left(&ident_id).unwrap(),
                                param_types
                                    .iter()
                                    .map(|t| self.find_type_by_type_id(*t))
                                    .map(Type::to_string)
                                    .collect::<Vec<String>>()
                                    .join(", ")
                            ),
                            ident_ref.ident.span.clone(),
                            (file!(), line!()),
                        );
                    }
                    RequiredSymbolKind::Struct | RequiredSymbolKind::Other => {
                        self.diagnostics.report_err(
                            format!(
                                "Identifier '{}' not found",
                                self.identifiers
                                    .get_by_left(&ident_id)
                                    .expect("Identifier {ident_id} found")
                            ),
                            ident_ref.ident.span.clone(),
                            (file!(), line!()),
                        );
                    }
                }

                // still, resolve it to an unknown symbol
                self.identifier_refs
                    .insert(ident_ref.id, ident_ref.resolved(self.not_found_symbol_id));

                Vec::new()
            }
        }
    }

    fn resolve_access(
        &mut self,
        hir: &mut UnresolvedHir,
        span: &Span,
        expr_id: ExprId,
        ident_ref_id: IdentRefId,
        ident_ref_kind: RequiredSymbolKind,
    ) -> (TypeId, Option<SymbolId>) {
        let (expr_type_id, symbol_id) = self.resolve_expression(hir, expr_id);

        // todo:feature make sure that fq names start form the root namespace (resolve_expression
        //  crawl the scoped up until it finds the symbol, but we don't want to start descending
        //  the scope tree from an "intermediate" (i.e. no root) level

        let ident_ref = hir
            .identifier_refs
            .remove(ident_ref_id)
            .expect("ident_ref exists");

        // Two things can happen during the `resolve_expression` call:
        // - If the `symbol_id` exists, we have a direct ref to a symbol, and we can use it to find
        //   everything we need to continue. This is the case when we use a variable for instance:
        //   it has a symbol and its id is returned by `resolve_expression`.
        // - If the `symbol_id` does not exist, we may be in the case where the access thing is
        //   returned dynamically (by an if expression for instance) and in that case we need to
        //   look things up by the `type_id`.
        //
        // Note: Usually we don't need to worry about the symbol id as everything should have a
        // valid type, but as namespaces have `void` type, we need to work with the symbol_id too.

        // so, if we have a symbol_id, and it corresponds to a namespace, we use it
        #[allow(unused_variables)] // used in #[cfg(test)]
        if let Some((symbol_id, SymbolKind::Namespace(ns_ident_id, symbols))) =
            symbol_id.map(|id| (id, &self.symbols[id].kind))
        {
            #[cfg(test)]
            println!(
                "{}:{}: Searching for {:?} ({:?}) in {:?}",
                file!(),
                line!(),
                ident_ref.ident.id,
                ident_ref_kind,
                self.symbols[symbol_id]
            );
            let resolved_symbol_id =
                match symbols.find(&self.symbols, ident_ref.ident.id, ident_ref_kind) {
                    Some(symbol_id) => symbol_id,
                    None => {
                        match ident_ref_kind {
                            RequiredSymbolKind::Function(param_types) => {
                                self.diagnostics.report_err(
                                    format!(
                                    "No function '{}' found for parameters of types ({}) in '{}'",
                                    self.identifiers.get_by_left(&ident_ref.ident.id).unwrap(),
                                    param_types
                                        .iter()
                                        .map(|t| self.find_type_by_type_id(*t))
                                        .map(Type::to_string)
                                        .collect::<Vec<String>>()
                                        .join(", "),
                                    self.identifiers.get_by_left(ns_ident_id).unwrap(),
                                ),
                                    ident_ref.ident.span.clone(),
                                    (file!(), line!()),
                                );
                            }
                            RequiredSymbolKind::Struct | RequiredSymbolKind::Other => {
                                self.diagnostics.report_err(
                                    format!(
                                        "No symbol '{}' found in '{}'",
                                        self.identifiers.get_by_left(&ident_ref.ident.id).unwrap(),
                                        self.identifiers.get_by_left(ns_ident_id).unwrap(),
                                    ),
                                    ident_ref.ident.span.clone(),
                                    (file!(), line!()),
                                )
                            }
                        }

                        self.not_found_symbol_id
                    }
                };

            let ident_ref = ident_ref.resolved(resolved_symbol_id);
            self.identifier_refs.insert(ident_ref.id, ident_ref);
            return (expr_type_id, Some(resolved_symbol_id));
        }

        // otherwise, we use the type_id
        let ty = self.find_type_by_type_id(expr_type_id);
        match ty {
            Type::Struct(stmt_id, _) if matches!(ident_ref_kind, RequiredSymbolKind::Other) => {
                let stmt_id = *stmt_id;
                if let Some(stmt) = hir.statements.remove(stmt_id) {
                    self.resolve_statement(hir, stmt);
                }

                match &self.statements[stmt_id].kind {
                    StatementKind::Struct(ident, _, _, Implementation::Provided(fields), _) => {
                        match fields
                            .iter()
                            .enumerate()
                            .find(|(_, field)| field.identifier.id == ident_ref.ident.id)
                        {
                            Some((index, field)) => {
                                let field_symbol_id = self
                                    .find_symbol_id_for_struct_field(stmt_id, index)
                                    .expect("field exists");
                                let ident_ref = ident_ref.resolved(field_symbol_id);
                                let symbol_ids = ident_ref.resolved_symbol_ids().to_vec();
                                assert_eq!(symbol_ids.len(), 1);
                                self.identifier_refs.insert(ident_ref.id, ident_ref);
                                (field.resolved_type_id(), Some(symbol_ids[0]))
                            }
                            None => {
                                self.diagnostics.report_err(
                                    format!(
                                        "No field '{}' found in struct {}",
                                        self.identifiers.get_by_left(&ident_ref.ident.id).unwrap(),
                                        self.identifiers.get_by_left(&ident.id).unwrap()
                                    ),
                                    ident_ref.ident.span.clone(),
                                    (file!(), line!()),
                                );
                                let ident_ref = ident_ref.resolved(self.not_found_symbol_id);
                                self.identifier_refs.insert(ident_ref.id, ident_ref);
                                (self.find_type_id_by_type(&Type::Invalid), None)
                            }
                        }
                    }
                    StatementKind::Struct(ident, ..) => {
                        self.diagnostics.report_err(
                            format!(
                                "Native struct {} fields cannot be accessed",
                                self.identifiers.get_by_left(&ident.id).unwrap()
                            ),
                            span.clone(),
                            (file!(), line!()),
                        );
                        (self.find_type_id_by_type(&Type::Invalid), None)
                    }
                    _ => panic!("struct expected"),
                }
            }
            _ => {
                let type_id = self.find_type_id_by_type(ty);
                match self
                    .type_functions
                    .get(&type_id)
                    .and_then(|functions| functions.get(&ident_ref.ident.id))
                {
                    // todo make sure the function params type match
                    Some(symbol_id) => {
                        let ident_ref = ident_ref.resolved(*symbol_id);
                        self.identifier_refs.insert(ident_ref.id, ident_ref);
                        (self.symbols[*symbol_id].type_id, Some(*symbol_id))
                    }
                    None => {
                        match ident_ref_kind {
                            RequiredSymbolKind::Function(_) => {
                                self.diagnostics.report_err(
                                    format!(
                                        "Function '{}' not found",
                                        self.identifiers
                                            .get_by_left(&ident_ref.ident.id)
                                            .expect("ident exists")
                                    ),
                                    ident_ref.ident.span.clone(),
                                    (file!(), line!()),
                                );
                            }
                            RequiredSymbolKind::Struct => self.diagnostics.report_err(
                                format!("Expected struct type, got {}", ty),
                                self.expressions[expr_id].span.clone(),
                                (file!(), line!()),
                            ),
                            RequiredSymbolKind::Other => self.diagnostics.report_err(
                                format!("Expected namespace or struct type, got {}", ty),
                                self.expressions[expr_id].span.clone(),
                                (file!(), line!()),
                            ),
                        }

                        // this it not always true (the left hand side can be a symbol), but it not
                        // being a struct field anyway, considering we did not find any symbol is
                        // (probably) fine...
                        let ident_ref = ident_ref.resolved(self.not_found_symbol_id);
                        self.identifier_refs.insert(ident_ref.id, ident_ref);
                        (self.find_type_id_by_type(&Type::Invalid), None)
                    }
                }
            }
        }
    }

    fn resolve_function_call(
        &mut self,
        hir: &mut UnresolvedHir,
        expr_id: ExprId,
        params: &[ExprId],
    ) -> TypeId {
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        let mut param_types = Vec::with_capacity(params.len());
        for param in params {
            let param_type = self.resolve_expression(hir, *param).0;

            if param_type != invalid_type_id {
                param_types.push(param_type)
            }
        }

        if param_types.len() != params.len() {
            return invalid_type_id;
        }

        if let Some(expr) = self.expressions.get(expr_id) {
            return expr.resolved_type_id();
        }

        let expr = hir
            .expressions
            .remove(expr_id)
            .expect("expr is not resolved");

        let (fn_type_id, symbol_id) = match &expr.kind {
            ExpressionKind::Literal(Literal {
                kind: LiteralKind::Identifier(ident_ref),
                ..
            }) => {
                let symbol_ids = self.resolve_ident_ref(
                    hir,
                    *ident_ref,
                    RequiredSymbolKind::Function(&param_types),
                );
                debug_assert!(symbol_ids.len() <= 1);
                let type_id = symbol_ids
                    .first()
                    .map(|s| self.symbols[*s].type_id)
                    .unwrap_or(invalid_type_id);

                (type_id, symbol_ids.first().cloned())
            }
            ExpressionKind::Access(expr_id, ident_ref_id) => self.resolve_access(
                hir,
                &expr.span,
                *expr_id,
                *ident_ref_id,
                RequiredSymbolKind::Function(&param_types),
            ),
            kind => panic!("expected literal or access, got {:?}", kind),
        };

        self.expressions.insert(expr_id, expr.typed(fn_type_id));

        symbol_id
            .map(|symbol_id| match &self.symbols[symbol_id].kind {
                SymbolKind::LetFn(_, _, _, ret_type) => *ret_type,
                SymbolKind::Native(_, _, ret_type, _) => *ret_type,
                SymbolKind::NotFound => invalid_type_id,
                _ => unreachable!("we resolved the ident_ref as a function"),
            })
            .unwrap_or_else(|| invalid_type_id)
    }

    fn resolve_while(
        &mut self,
        hir: &mut UnresolvedHir,
        cond: ExprId,
        expr: ExprId,
    ) -> (TypeId, Option<SymbolId>) {
        let cond_type = self.resolve_expression(hir, cond).0;
        let boolean_type_id = self.find_type_id_by_type(&Type::Boolean);
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        if cond_type != boolean_type_id && cond_type != invalid_type_id {
            self.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    self.find_type_by_type_id(cond_type)
                ),
                self.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        self.resolve_expression(hir, expr)
    }

    fn resolve_block(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) -> TypeId {
        self.scopes.push();

        self.insert_functions(hir, stmts, false);
        let stmts_type_id = self.resolve_statements(hir, stmts);

        self.scopes.pop();

        stmts_type_id
    }

    fn resolve_struct_instantiation(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref_id: IdentRefId,
        type_parameters: &Vec<TypeDefId>,
        field_exprs: &[(IdentRefId, ExprId)],
        span: &Span,
    ) -> TypeId {
        let mut expr_type_ids = Vec::with_capacity(field_exprs.len());
        for (_, field_expr_id) in field_exprs {
            let expr_type_id = self.resolve_expression(hir, *field_expr_id);
            expr_type_ids.push(expr_type_id);
        }
        debug_assert!(expr_type_ids.len() == field_exprs.len());

        let struct_stmt_ids = self
            .resolve_ident_ref(hir, ident_ref_id, RequiredSymbolKind::Struct)
            .into_iter()
            .map(|sid| self.symbols[sid].as_struct().1)
            .collect::<Vec<_>>();

        debug_assert!(struct_stmt_ids.len() <= 1);

        let struct_stmt_id = match struct_stmt_ids.first() {
            None => return self.find_type_id_by_type(&Type::Invalid),
            Some(stmt_id) => {
                if let Some(stmt) = hir.statements.remove(*stmt_id) {
                    self.resolve_statement(hir, stmt);
                }
                *stmt_id
            }
        };

        let (struct_identifier, _, type_parameters, implementation, ..) =
            self.statements[struct_stmt_id].as_struct();

        if !type_parameters.is_empty() {
            todo!("Use {type_parameters:?}")
        }

        let field_types = match implementation {
            Implementation::Provided(field_types) => field_types,
            _ => {
                self.diagnostics.report_err(
                    format!(
                        "Native struct {} cannot be instantiated",
                        self.identifiers.get_by_left(&struct_identifier.id).unwrap()
                    ),
                    span.clone(),
                    (file!(), line!()),
                );
                &Default::default()
            }
        };

        if field_exprs.len() != field_types.len() {
            self.diagnostics.report_err(
                "Struct fields differ in length",
                span.clone(),
                (file!(), line!()),
            );
        }

        for ((field_ident_ref_id, field_expr_id), (expr_type_id, _)) in
            field_exprs.iter().zip(expr_type_ids.into_iter())
        {
            let field_ident_ref = hir
                .identifier_refs
                .remove(*field_ident_ref_id)
                .expect("field ident_ref exists");

            if let Some((index, field)) = field_types
                .iter()
                .enumerate()
                .find(|(_, field)| field.identifier.id == field_ident_ref.ident.id)
            {
                let field_symbol_id = self
                    .find_symbol_id_for_struct_field(struct_stmt_id, index)
                    .expect("symbol exists");

                self.identifier_refs.insert(
                    *field_ident_ref_id,
                    field_ident_ref.resolved(field_symbol_id),
                );

                if expr_type_id != field.resolved_type_id() {
                    self.diagnostics.report_err(
                        format!(
                            "Invalid type for field '{}': expected {}, got {}",
                            self.identifiers.get_by_left(&field.identifier.id).unwrap(),
                            self.find_type_by_type_id(field.resolved_type_id()),
                            self.find_type_by_type_id(expr_type_id)
                        ),
                        self.expressions[*field_expr_id].span.clone(),
                        (file!(), line!()),
                    )
                }
            } else {
                // the field was not found by its name...
                self.identifier_refs.insert(
                    *field_ident_ref_id,
                    field_ident_ref.resolved(self.not_found_symbol_id),
                );
            }
        }

        // todo!(
        //     "this is not correct, we need to find the type where the type parameters are resolved"
        // );
        self.find_type_id_by_identifier(struct_identifier.id, vec![])
            .expect("type exists")
    }

    fn resolve_array_instantiation(
        &mut self,
        hir: &mut UnresolvedHir,
        values: &[ExprId],
    ) -> TypeId {
        let expected_type_id = self
            .resolve_expression(
                hir,
                *values.first().expect("array has at least one element"),
            )
            .0;

        if matches!(
            self.types.get_by_left(&expected_type_id).unwrap(),
            Type::Void
        ) {
            self.diagnostics.report_err(
                "Void values cannot be used as array elements at index 0".to_string(),
                self.expressions[*values.first().unwrap()].span.clone(),
                (file!(), line!()),
            );
            return self.find_type_id_by_type(&Type::Invalid);
        }

        for (index, expr_id) in values.iter().enumerate().skip(1) {
            let type_id = self.resolve_expression(hir, *expr_id).0;
            if type_id != expected_type_id {
                self.diagnostics.report_err(
                    format!(
                        "Expected value of type {expected_type}, got {actual_type} at index {index}",
                        expected_type = self.find_type_by_type_id(expected_type_id),
                        actual_type = self.find_type_by_type_id(type_id)
                    ),
                    self.expressions[*expr_id].span.clone(),
                    (file!(), line!()),
                );
            }
        }

        self.insert_type(Type::Array(expected_type_id, values.len()))
    }

    fn resolve_array_access(
        &mut self,
        hir: &mut UnresolvedHir,
        base_expr_id: ExprId,
        value_expr_id: ExprId,
    ) -> TypeId {
        let array_type_id = self.resolve_expression(hir, base_expr_id).0;
        let array_type = self.find_type_by_type_id(array_type_id);

        let type_id = match array_type {
            Type::Array(elements_type_id, _) => *elements_type_id,
            _ => {
                self.diagnostics.report_err(
                    format!("Expected type array, got {}", array_type),
                    self.expressions[base_expr_id].span.clone(),
                    (file!(), line!()),
                );
                self.find_type_id_by_type(&Type::Invalid)
            }
        };

        let index_type_id = self.resolve_expression(hir, value_expr_id).0;
        if !matches!(self.find_type_by_type_id(index_type_id), Type::Number) {
            self.diagnostics.report_err(
                format!(
                    "Expected index to be of type number, got {}",
                    self.find_type_by_type_id(index_type_id)
                ),
                self.expressions[base_expr_id].span.clone(),
                (file!(), line!()),
            );
        }

        type_id
    }

    fn resolve_statements(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) -> TypeId {
        let mut ret_type = self.find_type_id_by_type(&Type::Void);

        for &stmt_id in stmts {
            let stmt_type = if let Some(stmt) = hir.statements.remove(stmt_id) {
                if matches!(stmt.kind, StatementKind::Namespace(..)) {
                    self.diagnostics.report_err(
                        "Namespace invalid at this location",
                        stmt.span.clone(),
                        (file!(), line!()),
                    );
                    return self.find_type_id_by_type(&Type::Invalid);
                }
                self.resolve_statement(hir, stmt)
            } else {
                let stmt = self
                    .statements
                    .get(stmt_id)
                    .expect("no unbound statement found");
                match &stmt.kind {
                    StatementKind::Expression(e) => self
                        .expressions
                        .get(*e)
                        .expect("expression was visited")
                        .resolved_type_id(),
                    StatementKind::Let(..) => self.find_type_id_by_type(&Type::Void),
                    StatementKind::Ret(..) => self.find_type_id_by_type(&Type::None),
                    StatementKind::LetFn(..) => self.find_type_id_by_type(&Type::Void),
                    StatementKind::Struct(..) => self.find_type_id_by_type(&Type::Void),
                    StatementKind::Annotation(..) => self.find_type_id_by_type(&Type::Void),
                    StatementKind::Use(..) => self.find_type_id_by_type(&Type::Void),
                    StatementKind::Namespace(..) => {
                        unreachable!("namespace invalid at this location")
                    }
                }
            };

            if ret_type != self.find_type_id_by_type(&Type::None) {
                ret_type = stmt_type
            }
        }

        ret_type
    }

    fn resolve_statement(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt: Statement<Untyped, Unbound>,
    ) -> TypeId {
        let stmt_id = stmt.id;
        let span = stmt.span.clone();

        match stmt.kind {
            StatementKind::Expression(expr) => {
                self.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Expression(expr), span),
                );

                self.resolve_expression(hir, expr).0
            }
            StatementKind::Let(ident, expr) => {
                let symbol_id = self.resolve_let(hir, stmt_id, &ident, expr);

                self.statements.insert(
                    stmt_id,
                    Statement::new(
                        stmt_id,
                        StatementKind::Let(ident.bind(symbol_id), expr),
                        span,
                    ),
                );

                self.find_type_id_by_type(&Type::Void)
            }
            StatementKind::Ret(expr, ret_mode) => {
                if let Some(expr) = expr {
                    self.resolve_expression(hir, expr);
                }

                self.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Ret(expr, ret_mode), span),
                );

                self.find_type_id_by_type(&Type::None)
            }
            StatementKind::LetFn(
                ident,
                annotations,
                params,
                ret_type,
                Implementation::Provided(expr),
                _,
            ) => {
                let (identifier, parameters, ret_type, implementation) = self.resolve_function(
                    hir,
                    stmt_id,
                    (ident, params, ret_type, Implementation::Provided(expr)),
                    &annotations,
                    &span,
                );

                self.statements.insert(
                    stmt_id,
                    Statement::new(
                        stmt_id,
                        StatementKind::LetFn(
                            identifier,
                            annotations,
                            parameters,
                            ret_type,
                            implementation,
                            self.current_fn.last().cloned(),
                        ),
                        span,
                    ),
                );

                self.find_type_id_by_type(&Type::Void)
            }
            #[cfg(debug_assertions)]
            StatementKind::LetFn(_, _, _, _, Implementation::Native(_), _) => {
                panic!("body type must be implemented before resolution");
            }
            #[cfg(not(debug_assertions))]
            StatementKind::LetFn(_, _, _, _, Implementation::Native, _) => {
                panic!("body type must be implemented before resolution");
            }
            StatementKind::Struct(ident, annotations, type_parameters, implementation, _) => {
                let fields = implementation.get();
                let (ident, type_parameters, fields) =
                    self.resolve_struct(hir, stmt_id, ident, type_parameters, fields, &annotations);

                self.statements.insert(
                    stmt_id,
                    Statement::new(
                        stmt_id,
                        StatementKind::Struct(
                            ident,
                            annotations,
                            type_parameters,
                            fields,
                            self.current_fn.last().cloned(),
                        ),
                        span,
                    ),
                );

                self.find_type_id_by_type(&Type::Void)
            }
            StatementKind::Annotation(ident) => {
                let ident = self.resolve_annotation(hir, stmt_id, ident);

                self.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Annotation(ident), span),
                );

                self.find_type_id_by_type(&Type::Void)
            }
            StatementKind::Use(ident_ref_ids) => {
                self.resolve_use(hir, &ident_ref_ids);

                self.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Use(ident_ref_ids), span),
                );

                self.find_type_id_by_type(&Type::Void)
            }
            StatementKind::Namespace(ident, input_id, stmts) => {
                let ident = self.resolve_namespace(hir, stmt_id, ident, &stmts);

                self.statements.insert(
                    stmt_id,
                    Statement::new(
                        stmt_id,
                        StatementKind::Namespace(ident, input_id, stmts),
                        span,
                    ),
                );

                self.scopes.pop();

                self.find_type_id_by_type(&Type::Void)
            }
        }
    }

    fn resolve_let(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt: StmtId,
        ident: &Identifier<Unbound>,
        expr: ExprId,
    ) -> SymbolId {
        let expr_type_id = self.resolve_expression(hir, expr).0;

        if expr_type_id == self.find_type_id_by_type(&Type::None) {
            let expr = &self.expressions[expr];
            self.diagnostics.report_err(
                format!("Expected some type, got {}", Type::None),
                expr.span.clone(),
                (file!(), line!()),
            );
        }
        if expr_type_id == self.find_type_id_by_type(&Type::Void) {
            let expr = &self.expressions[expr];
            self.diagnostics.report_err(
                format!("Expected some type, got {}", Type::Void),
                expr.span.clone(),
                (file!(), line!()),
            );
        }

        self.insert_symbol(ident.id, SymbolKind::Let(ident.id, stmt), expr_type_id)
    }

    /// Resolves a function, starting by inserting all structs contained in the function (but not
    /// in nested functions). See `insert_structs`.
    fn resolve_function(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt_id: StmtId,
        (ident, params, ret_type, implementation): Function<Untyped, Unbound>,
        annotations: &[Annotation],
        _span: &Span,
    ) -> Function<Typed, Bound> {
        let body_expr_id = implementation.get();
        self.current_fn.push(stmt_id);
        self.scopes.push();

        if let ExpressionKind::Block(stmt_ids) = &hir.expressions[body_expr_id].kind {
            let stmt_ids = stmt_ids
                .iter()
                .filter(|stmt_id| {
                    matches!(hir.statements[**stmt_id].kind, StatementKind::Struct(..))
                })
                .copied()
                .collect::<Vec<StmtId>>();
            self.insert_structs(hir, &stmt_ids);
        }

        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        let (fn_symbol_id, param_types, ret_type_id) = self
            .function_symbols
            .get(&stmt_id)
            .cloned()
            .map(|symbol_id| {
                let (param_types, ret_type_id) = self.symbols[symbol_id].as_function();
                let param_types = param_types.clone();
                (symbol_id, param_types, ret_type_id)
            })
            // it may happen that the function is not found in case of duplicate def.
            .unwrap_or({
                let mut params = Vec::with_capacity(params.len());
                params.resize(params.len(), invalid_type_id);
                (self.not_found_symbol_id, params, invalid_type_id)
            });

        #[cfg(test)]
        println!(
            "{}:{}: Visiting function {name} ({fn_symbol_id:?}) with return type {ret_type} in scope {scope}",
            file!(),
            line!(),
            name = self.identifiers.get_by_left(&ident.id).unwrap(),
            ret_type = self.types.get_by_left(&ret_type_id).unwrap(),
            scope = self.scopes.len()
        );

        let parameters = params
            .into_iter()
            .zip(param_types)
            .enumerate()
            .filter_map(|(index, (parameter, type_id))| {
                let ident_id = parameter.identifier.id;
                let symbol_kind = SymbolKind::Parameter(ident_id, stmt_id, index);

                if self.is_symbol_in_current_scope(ident_id, &symbol_kind) {
                    self.diagnostics.report_err(
                        format!(
                            "Parameter '{ident}' is already defined",
                            ident = self.identifiers.get_by_left(&ident_id).unwrap(),
                        ),
                        parameter.identifier.span.clone(),
                        (file!(), line!()),
                    );
                    None
                } else {
                    let symbol_id = self.insert_symbol(ident_id, symbol_kind, type_id);

                    Some(parameter.bind(type_id, symbol_id))
                }
            })
            .collect::<Vec<Parameter<Typed, Bound>>>();

        for annotation in annotations.iter() {
            self.resolve_ident_refs(hir, &annotation.ident_ref_ids, false);
        }

        let is_native = self.is_native_annotation_present(annotations);
        if is_native {
            let expression = &hir.expressions[body_expr_id];
            let has_body = match &expression.kind {
                ExpressionKind::Block(stmt_ids) => {
                    // because the implicit ret runs before the resolution, empty function
                    // bodies actually have exactly one implicit ret none.
                    !(stmt_ids.len() == 1
                        && matches!(
                            &hir.statements[stmt_ids[0]].kind,
                            &StatementKind::Ret(None, RetMode::Implicit)
                        ))
                }
                _ => true,
            };

            if has_body {
                self.diagnostics.report_err(
                    format!(
                        "Native function {} must not have a body",
                        self.identifiers.get_by_left(&ident.id).unwrap(),
                    ),
                    expression.span.clone(),
                    (file!(), line!()),
                );
            }
        }

        // we want to visit the expression, hence no short-circuit
        // note that we resolve the expression even for native function (even though we don't
        // report any error whatsoever so that we don't have "holes" in the resolved expressions)
        self.resolve_expression(hir, body_expr_id);

        if !is_native && ret_type_id != invalid_type_id {
            let exit_points = hir
                .exit_points
                .exit_points
                .get(&body_expr_id)
                .expect("exit points is computed")
                .iter()
                .map(|e| match e {
                    ExitPoint::Explicit(e) => (*e, true),
                    ExitPoint::Implicit(e) => (*e, false),
                })
                .collect::<Vec<_>>();

            if exit_points.is_empty() {
                panic!("we must always have at least one exit point, even if implicit and void");
            }

            #[cfg(test)]
            println!(
                "{}:{}: Exit points of {name} ({body_expr_id:?}): {exit_points:?}",
                file!(),
                line!(),
                name = self.identifiers.get_by_left(&ident.id).unwrap(),
            );

            for (exit_expr_id, explicit) in exit_points {
                let expr_type_id = match exit_expr_id {
                    None => self.find_type_id_by_type(&Type::Void),
                    Some(exit_expr_id) => self.resolve_expression(hir, exit_expr_id).0,
                };

                if expr_type_id == invalid_type_id {
                    // nothing to report, that was reported already
                } else if expr_type_id == self.find_type_id_by_type(&Type::None) {
                    panic!("functions must not return {}", Type::None)
                } else if expr_type_id != ret_type_id
                    && (ret_type_id != self.find_type_id_by_type(&Type::Void) || explicit)
                {
                    let expr_type = self.find_type_by_type_id(expr_type_id);
                    // fixme:span the span is not accurate (in both cases)
                    let span = if let Some(exit_expr_id) = exit_expr_id {
                        self.expressions[exit_expr_id].span.clone()
                    } else {
                        self.expressions[body_expr_id].span.clone()
                    };

                    self.diagnostics.report_err(
                        format!(
                            "Function {name} expected to return type {ret_type}, got {expr_type}",
                            name = self.identifiers.get_by_left(&ident.id).unwrap(),
                            ret_type = self.types.get_by_left(&ret_type_id).unwrap()
                        ),
                        span,
                        (file!(), line!()),
                    );
                }
            }
        }

        self.current_fn.pop();
        self.scopes.pop();

        (
            ident.bind(fn_symbol_id),
            parameters,
            ret_type.typed(ret_type_id),
            if is_native {
                #[cfg(debug_assertions)]
                {
                    Implementation::Native(body_expr_id)
                }
                #[cfg(not(debug_assertions))]
                {
                    Implementation::Native
                }
            } else {
                Implementation::Provided(body_expr_id)
            },
        )
    }

    fn resolve_struct(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt_id: StmtId,
        identifier: Identifier<Unbound>,
        type_parameters: Vec<Identifier<Unbound>>,
        fields: Vec<Field<Untyped, Unbound>>,
        annotations: &[Annotation],
    ) -> (
        Identifier<Bound>,
        Vec<Identifier<Bound>>,
        Implementation<Vec<Field<Typed, Bound>>>,
    ) {
        for annotation in annotations {
            self.resolve_ident_refs(hir, &annotation.ident_ref_ids, false);
        }

        let type_parameters = type_parameters
            .into_iter()
            .map(|tp| {
                let type_id = self.find_type_id_by_type(&Type::Number);
                let symbol_id =
                    self.insert_symbol(tp.id, SymbolKind::TypeParameter(tp.id, stmt_id), type_id);
                tp.bind(symbol_id)
            })
            .collect::<Vec<_>>();

        if !type_parameters.is_empty() {
            let type_parameters = type_parameters
                .iter()
                .map(|ident| ident.resolved_symbol_id())
                .map(|symbol_id| &self.symbols[symbol_id])
                .map(|symbol| symbol.type_id)
                .collect::<Vec<_>>();

            todo!("do something with {type_parameters:?}")
        }

        let is_native = self.is_native_annotation_present(annotations);
        if is_native && !fields.is_empty() {
            self.diagnostics.report_err(
                format!(
                    "Native struct {} must not have a body",
                    self.identifiers.get_by_left(&identifier.id).unwrap(),
                ),
                fields
                    .first()
                    .unwrap()
                    .span
                    .extend_to(&fields.last().unwrap().span),
                (file!(), line!()),
            );
        }

        // we resolve the typedefs
        for field in fields.iter() {
            self.resolve_type_def(hir, field.type_def_id, false);
        }

        let fields = fields
            .into_iter()
            .map(|field| {
                let type_id = self
                    .find_type_id_by_type_def_id(hir, field.type_def_id)
                    .unwrap_or(self.find_type_id_by_type(&Type::Invalid));

                field.typed(type_id)
            })
            .collect::<Vec<Field<Typed, Unbound>>>();

        // struct fields are in the scope of the struct itself, we want to make sure that no other
        // field with the same name exists in the current struct, but the same identifier might
        // exist outside and this is not an issue
        self.scopes.push();

        let fields = fields
            .into_iter()
            .enumerate()
            .map(|(index, field)| {
                let ident_id = field.identifier.id;
                let symbol_kind = SymbolKind::Field(ident_id, stmt_id, index);

                if self.is_symbol_in_current_scope(ident_id, &symbol_kind) {
                    self.diagnostics.report_err(
                        format!(
                            "Field '{ident}' is already defined",
                            ident = self.identifiers.get_by_left(&ident_id).unwrap(),
                        ),
                        field.identifier.span.clone(),
                        (file!(), line!()),
                    );
                    field.bind(self.not_found_symbol_id)
                } else {
                    let symbol_id =
                        self.insert_symbol(ident_id, symbol_kind, field.resolved_type_id());
                    field.bind(symbol_id)
                }
            })
            .collect::<Vec<Field<Typed, Bound>>>();

        self.scopes.pop();

        let symbol_id = self
            .struct_symbols
            .get(&stmt_id)
            .cloned()
            // it may happen that the struct is not found in case of duplicate def.
            .unwrap_or(self.not_found_symbol_id);

        (
            identifier.bind(symbol_id),
            type_parameters,
            if is_native {
                #[cfg(debug_assertions)]
                {
                    Implementation::Native(fields)
                }
                #[cfg(not(debug_assertions))]
                {
                    Implementation::Native
                }
            } else {
                Implementation::Provided(fields)
            },
        )
    }

    fn resolve_annotation(
        &mut self,
        _hir: &mut UnresolvedHir,
        stmt_id: StmtId,
        identifier: Identifier<Unbound>,
    ) -> Identifier<Bound> {
        let symbol_id = self
            .annotation_symbols
            .get(&stmt_id)
            .cloned()
            // it may happen that the annotation is not found in case of duplicate def.
            .unwrap_or(self.not_found_symbol_id);

        identifier.bind(symbol_id)
    }

    fn resolve_use(&mut self, hir: &mut UnresolvedHir, ident_ref_ids: &[IdentRefId]) {
        self.resolve_ident_refs(hir, ident_ref_ids, false);

        let ident_id = self.identifier_refs[*ident_ref_ids.last().unwrap()]
            .ident
            .id;

        self.identifier_refs[*ident_ref_ids.last().unwrap()]
            .ident
            .resolved_symbol_ids()
            .iter()
            .for_each(|id| self.scopes.push_symbol(ident_id, *id));
    }

    fn resolve_namespace(
        &mut self,
        hir: &mut UnresolvedHir,
        namespace_stmt_id: StmtId,
        identifier: Identifier<Unbound>,
        stmts: &[StmtId],
    ) -> Identifier<Bound> {
        self.scopes.push();

        let namespace_symbol_id = *self.namespace_symbols.get(&namespace_stmt_id).unwrap();
        self.bring_namespace_symbols_into_scope(namespace_symbol_id);

        for stmt_id in stmts.iter() {
            if let Some(statement) = hir.statements.remove(*stmt_id) {
                self.resolve_statement(hir, statement);
            }
        }

        let symbol_id = self
            .namespace_symbols
            .get(&namespace_stmt_id)
            .cloned()
            .unwrap_or(self.not_found_symbol_id);

        identifier.bind(symbol_id)
    }

    /// Resolve `ident_refs` involved in fully qualified names. Intermediate identifier refs are
    /// pointing to namespaces, final one to any kind of symbol. If `ignore_not_found` is `true`,
    /// no errors will be reported and the failed resolution will be put back in the
    /// `UnresolvedHir` so that a next phase can resolve them.
    fn resolve_ident_refs(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref_ids: &[IdentRefId],
        ignore_not_found: bool,
    ) {
        if ident_ref_ids.len() == 1 {
            self.resolve_ident_ref(hir, ident_ref_ids[0], RequiredSymbolKind::Other);
            return;
        }

        let mut parent_found = true;
        let mut namespace_id = *self.namespaces.root().unwrap();

        for ident_ref_id in ident_ref_ids[0..ident_ref_ids.len() - 1].iter() {
            if self.identifier_refs.get(*ident_ref_id).is_some() {
                continue;
            }

            let ident_ref = hir.identifier_refs.remove(*ident_ref_id).unwrap();

            if !parent_found {
                self.identifier_refs
                    .insert(*ident_ref_id, ident_ref.resolved(self.not_found_symbol_id));
                continue;
            }

            if let SymbolKind::Namespace(_, symbols) = &self.symbols[namespace_id].kind {
                if let Some(symbol_id) =
                    symbols.find(&self.symbols, ident_ref.ident.id, RequiredSymbolKind::Other)
                {
                    self.identifier_refs
                        .insert(*ident_ref_id, ident_ref.resolved(symbol_id));
                    namespace_id = symbol_id;
                    continue;
                }
            }

            if ignore_not_found {
                hir.identifier_refs.insert(*ident_ref_id, ident_ref);
                return;
            }

            if !ignore_not_found {
                self.diagnostics.report_err(
                    format!(
                        "Namespace '{}' not found",
                        self.identifiers.get_by_left(&ident_ref.ident.id).unwrap()
                    ),
                    ident_ref.ident.span.clone(),
                    (file!(), line!()),
                );
            }

            self.identifier_refs
                .insert(*ident_ref_id, ident_ref.resolved(self.not_found_symbol_id));
            parent_found = false;
        }

        let ident_ref_id = ident_ref_ids[ident_ref_ids.len() - 1];

        if self.identifier_refs.get(ident_ref_id).is_some() {
            return;
        }

        let ident_ref = hir.identifier_refs.remove(ident_ref_id).unwrap();

        if !parent_found {
            if ignore_not_found {
                hir.identifier_refs.insert(ident_ref_id, ident_ref);
            } else {
                self.identifier_refs
                    .insert(ident_ref_id, ident_ref.resolved(self.not_found_symbol_id));
            }
            return;
        }

        if !matches!(self.symbols[namespace_id].kind, SymbolKind::Namespace(..)) {
            if !ignore_not_found {
                let parent_ident_ref_id = ident_ref_ids[ident_ref_ids.len() - 2];
                let parent_ident_id = self
                    .identifier_refs
                    .get(parent_ident_ref_id)
                    .unwrap()
                    .ident
                    .id;

                self.diagnostics.report_err(
                    format!(
                        "Expected '{}' to be a namespace",
                        self.identifiers.get_by_left(&parent_ident_id).unwrap()
                    ),
                    self.identifier_refs[parent_ident_ref_id].ident.span.clone(),
                    (file!(), line!()),
                );
            }
            self.identifier_refs
                .insert(ident_ref_id, ident_ref.resolved(self.not_found_symbol_id));
            return;
        }

        let symbol_ids = self.symbols[namespace_id]
            .as_namespace()
            .get(&ident_ref.ident.id)
            .cloned()
            .unwrap_or_default();

        if !symbol_ids.is_empty() {
            self.identifier_refs
                .insert(ident_ref_id, ident_ref.resolved_multiple(symbol_ids));
        } else if ignore_not_found {
            hir.identifier_refs.insert(ident_ref_id, ident_ref);
        } else {
            self.diagnostics.report_err(
                format!(
                    "Symbol '{}' not found",
                    self.identifiers.get_by_left(&ident_ref.ident.id).unwrap()
                ),
                ident_ref.ident.span.clone(),
                (file!(), line!()),
            );
            self.identifier_refs
                .insert(ident_ref_id, ident_ref.resolved(self.not_found_symbol_id));
        }
    }

    /// Resolves a `TypeDefId`. Starts by resolving all potential `IdentRefId`s found and resolves
    /// the `TypeDefId` to that last found type. By default, issues a diagnostic when the type
    /// found is not assignable (as per `Type::is_assignable()` definition. If `return_type` is set
    /// to true however, the type validity is checked with `Type::is_valid_return_type()`.
    fn resolve_type_def(
        &mut self,
        hir: &mut UnresolvedHir,
        type_def_id: TypeDefId,
        return_type: bool,
    ) -> TypeId {
        match &hir.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                let ident_ref_ids = ident_ref_ids.clone(); // todo why clone()?
                self.resolve_ident_refs(hir, &ident_ref_ids, false);

                let ident_ref_id = *ident_ref_ids.last().unwrap();
                let symbol_ids = self.identifier_refs[ident_ref_id]
                    .ident
                    .resolved_symbol_ids();

                debug_assert_eq!(symbol_ids.len(), 1);
                let symbol_id = symbol_ids[0];

                let ty = match &self.symbols[symbol_id].kind {
                    SymbolKind::Struct(_, stmt_id) => {
                        let type_parameters_count = hir
                            .statements
                            .get(*stmt_id)
                            .map(|s| s.as_struct().2.len())
                            .unwrap_or_else(|| hir.statements[*stmt_id].as_struct().2.len());

                        Type::Struct(
                            *stmt_id,
                            vec![self.find_type_id_by_type(&Type::Type); type_parameters_count],
                        )
                    }
                    SymbolKind::NativeType(_, ty) => ty.clone(),
                    SymbolKind::NotFound => {
                        // nothing, we reported already
                        return self.find_type_id_by_type(&Type::Invalid);
                    }
                    _ => {
                        let ident = &self.identifier_refs[ident_ref_id].ident;
                        self.diagnostics.report_err(
                            format!(
                                "Expected {} to be a type",
                                self.identifiers.get_by_left(&ident.id).unwrap()
                            ),
                            ident.span.clone(),
                            (file!(), line!()),
                        );
                        return self.find_type_id_by_type(&Type::Invalid);
                    }
                };

                if !(return_type && ty.is_valid_return_type() || ty.is_assignable()) {
                    self.diagnostics.report_err(
                        format!("Type '{}' is not a valid type", ty),
                        hir.type_defs[type_def_id].span.clone(),
                        (file!(), line!()),
                    )
                }
            }
            TypeDefKind::Array(type_def_id, _) => {
                self.resolve_type_def(hir, *type_def_id, false);
            }
        }

        self.find_type_id_by_type_def_id(hir, type_def_id)
            .unwrap_or_else(|| self.find_type_id_by_type(&Type::Invalid))
    }

    fn is_native_annotation_present(&self, annotations: &[Annotation]) -> bool {
        for annotation in annotations.iter() {
            if annotation.ident_ref_ids.len() != NATIVE_ANNOTATION.len() {
                continue;
            }

            let match_len = NATIVE_ANNOTATION
                .iter()
                .zip(annotation.ident_ref_ids.iter())
                .map(|(&path, &id)| {
                    (
                        path,
                        self.identifiers
                            .get_by_left(&self.identifier_refs.get(id).unwrap().ident.id)
                            .unwrap(),
                    )
                })
                .take_while(|(left, right)| left == right)
                .count();

            if match_len != NATIVE_ANNOTATION.len() {
                continue;
            }

            let symbol_ids = self.identifier_refs[*annotation.ident_ref_ids.last().unwrap()]
                .resolved_symbol_ids();
            for symbol_id in symbol_ids {
                if matches!(self.symbols[*symbol_id].kind, SymbolKind::Annotation(..)) {
                    return true;
                }
            }
        }
        false
    }

    /// Returns `true` if a symbol of the same kind already exists in the current scope.
    fn is_symbol_in_current_scope(&self, ident_id: IdentId, kind: &SymbolKind) -> bool {
        // todo: review the "exists" meaning. make it coherent with find_symbol_*, and also with
        //  the FindSymbol trait
        // todo:feature manage duplicate functions (for whatever it means ... - at least same name
        //   same first parameter type)
        self.scopes
            .last_symbols_by_ident_id(ident_id)
            .iter()
            .map(|s| &self.symbols[*s])
            .any(|s| {
                matches!(
                    (&s.kind, kind),
                    (SymbolKind::LetFn(..), SymbolKind::LetFn(..))
                        | (SymbolKind::Parameter(..), SymbolKind::Parameter(..))
                        | (SymbolKind::Struct(..), SymbolKind::Struct(..))
                        | (SymbolKind::Field(..), SymbolKind::Field(..))
                        | (SymbolKind::Annotation(..), SymbolKind::Annotation(..))
                )
            })
    }

    fn insert_symbol(&mut self, ident_id: IdentId, kind: SymbolKind, ty: TypeId) -> SymbolId {
        let symbol_id = self.symbols.create();

        match &kind {
            SymbolKind::Parameter(_, stmt_id, index) | SymbolKind::Field(_, stmt_id, index) => {
                debug_assert!(self.scopes.len() > 1);
                self.stmt_symbols.insert((*stmt_id, *index), symbol_id);
            }
            _ => (),
        };

        self.symbols.insert(
            symbol_id,
            Symbol {
                id: symbol_id,
                kind,
                type_id: ty,
            },
        );

        self.scopes.push_symbol(ident_id, symbol_id);

        symbol_id
    }

    /// Inserts a namespace, walking down the children. Returns the `SymbolId` of the inserted
    /// namespace
    fn insert_namespace(&mut self, hir: &UnresolvedHir, stmt_id: StmtId) -> SymbolId {
        let statement = &hir.statements[stmt_id];
        let (namespace_ident, _, namespace_stmts) = statement.as_namespace();

        if let Some(namespace_symbol_id) = self.namespaces.last() {
            if self.symbols[*namespace_symbol_id]
                .as_namespace()
                .contains_key(&namespace_ident.id)
            {
                self.diagnostics.report_err(
                    format!(
                        "Identifier '{}' already used in the current namespace",
                        self.identifiers.get_by_left(&namespace_ident.id).unwrap()
                    ),
                    statement.span.clone(),
                    (file!(), line!()),
                );
            }
        }

        let symbol_id = self.insert_symbol(
            namespace_ident.id,
            SymbolKind::Namespace(namespace_ident.id, Default::default()),
            self.find_type_id_by_type(&Type::Void),
        );
        self.namespace_symbols.insert(stmt_id, symbol_id);

        self.bring_symbol_into_namespace(namespace_ident.id, symbol_id);

        self.namespaces.push(symbol_id);
        self.scopes.push();

        self.insert_namespaces(hir, namespace_stmts);
        self.insert_annotations(hir, namespace_stmts);
        self.insert_structs(hir, namespace_stmts);

        self.scopes.pop();
        self.namespaces.pop();

        symbol_id
    }

    fn insert_namespaces(&mut self, hir: &UnresolvedHir, stmts: &[StmtId]) {
        let namespaces = stmts
            .iter()
            .filter_map(|stmt| hir.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                StatementKind::Namespace(..) => Some(stmt.id),
                _ => None,
            })
            .collect::<Vec<_>>();

        namespaces.into_iter().for_each(|stmt| {
            self.insert_namespace(hir, stmt);
        });
    }

    fn insert_namespace_functions(&mut self, hir: &mut UnresolvedHir, stmt_id: StmtId) {
        self.namespaces
            .push(*self.namespace_symbols.get(&stmt_id).unwrap());
        self.scopes.push();

        let namespace_symbol_id = *self.namespace_symbols.get(&stmt_id).unwrap();
        self.bring_namespace_symbols_into_scope(namespace_symbol_id);

        let (_, _, stmts) = hir.statements[stmt_id].as_namespace();
        let stmts = stmts.clone();
        self.insert_namespaces_functions(hir, &stmts);
        self.insert_functions(hir, &stmts, true);

        self.scopes.pop();
        self.namespaces.pop();
    }

    /// Inserts all top level functions contained in namespaces which `StmtId` are provided.
    fn insert_namespaces_functions(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) {
        let namespaces = stmts
            .iter()
            .filter_map(|stmt| hir.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                StatementKind::Namespace(..) => Some(stmt.id),
                _ => None,
            })
            .collect::<Vec<_>>();

        namespaces
            .into_iter()
            .for_each(|stmt| self.insert_namespace_functions(hir, stmt));
    }

    /// Inserts all functions found in `stmts` into `self.function_symbols` (which itself contains
    /// reference to `self.symbols`) as well as the current scope's symbol table, and if
    /// `top_level` is `true` into the current namespace.
    fn insert_functions(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId], top_level: bool) {
        for stmt_id in stmts.iter() {
            let stmt = hir.statements.remove(*stmt_id).unwrap();

            match &stmt.kind {
                StatementKind::LetFn(ident, _, params, ret, ..) => {
                    let parameter_types = params
                        .iter()
                        .map(|p| p.type_def_id)
                        .map(|type_def_id| self.resolve_type_def(hir, type_def_id, false))
                        .collect::<Vec<_>>();

                    let ret_type = ret
                        .type_def_id
                        .map(|type_def_id| self.resolve_type_def(hir, type_def_id, true))
                        .unwrap_or(self.find_type_id_by_type(&Type::Void));

                    let symbol_kind =
                        SymbolKind::LetFn(ident.id, stmt.id, parameter_types.clone(), ret_type);

                    if self.is_symbol_in_current_scope(ident.id, &symbol_kind) {
                        self.diagnostics.report_err(
                            format!(
                                "Function '{ident}' is already defined in scope",
                                ident = self.identifiers.get_by_left(&ident.id).unwrap(),
                            ),
                            ident.span.clone(),
                            (file!(), line!()),
                        )
                    } else {
                        let target_type_id = parameter_types.first().cloned();

                        let fn_type_id =
                            self.insert_type(Type::Function(parameter_types, ret_type));

                        let symbol_id = self.insert_symbol(ident.id, symbol_kind, fn_type_id);

                        if top_level {
                            self.bring_symbol_into_namespace(ident.id, symbol_id);
                        }

                        self.function_symbols.insert(*stmt_id, symbol_id);
                        if let Some(target_type_id) = target_type_id {
                            self.type_functions
                                .entry(target_type_id)
                                .or_default()
                                .insert(ident.id, symbol_id);
                        }
                    }
                }
                StatementKind::Use(path) => {
                    self.resolve_ident_refs(hir, path, true);
                    if let Some(ident_ref) = self.identifier_refs.get(*path.last().unwrap()) {
                        let ident = &ident_ref.ident;
                        ident
                            .resolved_symbol_ids()
                            .iter()
                            .for_each(|id| self.scopes.push_symbol(ident.id, *id));
                    }
                }
                _ => (),
            }

            hir.statements.insert(*stmt_id, stmt);
        }
    }

    /// Inserts all structs found in `stmts` into `self.struct_symbols` (which itself contains
    /// reference to `self.symbols`) as well as the current stack frame's symbol table, and if
    /// `self.current_fn.last()` is `None` into the current namespace. While doing so, we perform
    /// the following:
    ///  - insert a type corresponding to the struct in `self.types`;
    ///  - verify that no struct with the same name already exist in the current scope;
    ///  - resolve the fields' types.
    fn insert_structs(&mut self, hir: &UnresolvedHir, stmts: &[StmtId]) {
        let structs = stmts
            .iter()
            .filter_map(|stmt| hir.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                StatementKind::Struct(ident, _, type_parameters, ..) => {
                    Some((stmt.id, ident.clone(), type_parameters.len()))
                }
                _ => None,
            })
            // todo get rid of the collect
            .collect::<Vec<(StmtId, Identifier<Unbound>, usize)>>();

        for (stmt_id, identifier, type_parameters) in structs.into_iter() {
            let ident_id = identifier.id;
            let symbol_kind = SymbolKind::Struct(ident_id, stmt_id);

            if self.is_symbol_in_current_scope(ident_id, &symbol_kind) {
                self.diagnostics.report_err(
                    format!(
                        "Struct '{ident}' is already defined in scope",
                        ident = self.identifiers.get_by_left(&ident_id).unwrap(),
                    ),
                    identifier.span.clone(),
                    (file!(), line!()),
                );
            } else {
                let types_parameters =
                    vec![self.find_type_id_by_type(&Type::Type); type_parameters];
                let struct_type_id = self.insert_type(Type::Struct(stmt_id, types_parameters));
                let symbol_id = self.insert_symbol(ident_id, symbol_kind, struct_type_id);

                if self.current_fn.last().is_none() {
                    self.bring_symbol_into_namespace(ident_id, symbol_id);
                }

                self.struct_symbols.insert(stmt_id, symbol_id);
            }
        }
    }

    /// Inserts all annotations found in `stmts` into `self.annotations_symbols` (which itself
    /// contains reference to `self.symbols`) as well as the current stack frame's symbol table,
    /// and into the current namespace.
    fn insert_annotations(&mut self, hir: &UnresolvedHir, stmts: &[StmtId]) {
        let annotations = stmts
            .iter()
            .filter_map(|stmt| hir.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                StatementKind::Annotation(ident) => Some((stmt.id, ident.clone())),
                _ => None,
            })
            .collect::<Vec<(StmtId, Identifier<Unbound>)>>();

        for (stmt_id, identifier) in annotations.into_iter() {
            let ident_id = identifier.id;
            let symbol_kind = SymbolKind::Annotation(ident_id, stmt_id);

            if self.is_symbol_in_current_scope(ident_id, &symbol_kind) {
                self.diagnostics.report_err(
                    format!(
                        "Annotation '{ident}' is already defined in scope",
                        ident = self.identifiers.get_by_left(&ident_id).unwrap(),
                    ),
                    identifier.span.clone(),
                    (file!(), line!()),
                )
            } else {
                let annotation_type_id = self.insert_type(Type::Void);
                let symbol_id = self.insert_symbol(ident_id, symbol_kind, annotation_type_id);

                self.bring_symbol_into_namespace(ident_id, symbol_id);

                self.annotation_symbols.insert(stmt_id, symbol_id);
            }
        }
    }

    /// Inserts a `Type` if it does not already exist and returns its `TypeId`. If the type already
    /// exists, returns its `TypeId`
    fn insert_type(&mut self, ty: Type) -> TypeId {
        if let Some(id) = self.types.get_by_right(&ty) {
            *id
        } else {
            let id = TypeId::from(self.types.len());
            let did_overwrite = self.types.insert(id, ty).did_overwrite();
            debug_assert!(!did_overwrite);
            id
        }
    }

    pub fn find_ident_id_by_str(&self, name: &str) -> IdentId {
        *self.identifiers.get_by_right(name).unwrap()
    }

    /// Finds the `TypeId` corresponding to a `TypeDefId`. Self is taken mutably in case we have an
    /// array for which we need to create a new `TypeId`.
    ///
    /// The assumption is that the provided `TypeDefId` is already fully resolved (through
    /// `resolve_type_def`).
    fn find_type_id_by_type_def_id(
        &mut self,
        hir: &UnresolvedHir,
        type_def_id: TypeDefId,
    ) -> Option<TypeId> {
        match &hir.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                // if ident_ref_ids.clone().len() == 1 {
                //     todo merge with the more general case in order to lift the documented
                //      assumption
                // let ident_id = self.identifier_refs[ident_ref_ids[0]].ident.id;
                //
                // self.find_type_id_by_identifier(ident_id)
                // } else {
                let symbol_id = self.find_symbol_by_ident_ref_ids(hir, ident_ref_ids)?;

                match &self.symbols[symbol_id].kind {
                    SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                    SymbolKind::Struct(_, stmt_id) => {
                        let type_parameters_count = hir
                            .statements
                            .get(*stmt_id)
                            .map(|s| s.as_struct().2.len())
                            .unwrap_or_else(|| hir.statements[*stmt_id].as_struct().2.len());

                        Some(self.find_type_id_by_type(&Type::Struct(
                            *stmt_id,
                            vec![self.find_type_id_by_type(&Type::Type); type_parameters_count],
                        )))
                    }
                    _ => None,
                }
                // }
            }
            TypeDefKind::Array(type_def_id, len) => self
                .find_type_id_by_type_def_id(hir, *type_def_id)
                .map(|base| Type::Array(base, *len))
                .map(|t| self.insert_type(t)),
        }
    }

    fn find_type_id_by_identifier(
        &self,
        ident_id: IdentId,
        type_parameters: Vec<TypeId>,
    ) -> Option<TypeId> {
        self.find_symbol_id_by_ident_and_kind(ident_id, RequiredSymbolKind::Other)
            .and_then(|symbol_id| match &self.symbols[symbol_id].kind {
                SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                SymbolKind::Struct(_, stmt) => {
                    Some(self.find_type_id_by_type(&Type::Struct(*stmt, type_parameters)))
                }
                _ => None,
            })
    }

    // todo:refactoring this is only used to find the TypeId of std.string.string (same as for
    //  self.types_by_name)...
    fn find_type_id_by_name(&mut self, name: &'static str) -> Option<TypeId> {
        fn find_symbol_by_name(resolver: &mut Resolver, name: &str) -> Option<SymbolId> {
            let path = name.split('.').collect::<Vec<&str>>();
            debug_assert!(!path.is_empty());

            if path.len() == 1 {
                todo!("Search for symbol in current scope, crawling up as needed")
            }

            let mut ns_symbols =
                resolver.symbols[*resolver.namespaces.root().unwrap()].as_namespace();
            for &name in &path[0..path.len() - 1] {
                let ident_id = *resolver.identifiers.get_by_right(name)?;
                let symbols = ns_symbols
                    .get(&ident_id)?
                    .iter()
                    .map(|sid| &resolver.symbols[*sid])
                    .filter(|s| matches!(s.kind, SymbolKind::Namespace(..)))
                    .collect::<Vec<_>>();

                debug_assert!(symbols.len() <= 1);

                ns_symbols = symbols.first()?.as_namespace();
            }

            let ident_id = resolver
                .identifiers
                .get_by_right(*path.last().unwrap())
                .unwrap();
            let symbols = ns_symbols.get(ident_id)?;

            debug_assert_eq!(symbols.len(), 1);
            symbols.first().cloned()
        }

        if let Some(type_id) = self.types_by_name.get(name) {
            return Some(*type_id);
        }

        let symbol_id = find_symbol_by_name(self, name)?;
        let type_id = self.symbols[symbol_id].type_id;
        self.types_by_name.insert(name, type_id);
        Some(type_id)
    }

    // todo:perf cache the result of predefined types directly in the Resolver?
    fn find_type_id_by_type(&self, ty: &Type) -> TypeId {
        *self.types.get_by_right(ty).unwrap()
    }

    fn find_type_by_type_id(&self, ty: TypeId) -> &Type {
        self.types
            .get_by_left(&ty)
            .unwrap_or_else(|| panic!("type {ty} exists"))
    }

    /// Resolves an identifier by its `IdentId` and returns the corresponding `SymbolId`. The
    /// resolution starts in the current scope and crawls the scopes stack up until the identifier
    /// is found.
    fn find_symbol_id_by_ident_and_kind(
        &self,
        ident: IdentId,
        kind: RequiredSymbolKind,
    ) -> Option<SymbolId> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.symbols.find(&self.symbols, ident, kind))
    }

    fn find_symbol_id_for_struct_field(&self, stmt_id: StmtId, index: usize) -> Option<SymbolId> {
        self.stmt_symbols
            .get(&(stmt_id, index))
            .and_then(|sid| self.symbols.get(*sid))
            .and_then(|s| match s.kind {
                SymbolKind::Field(..) => Some(s.id),
                _ => None,
            })
    }

    /// Finds the `SymbolId` that the `ident_ids` refer to. Does not try to resolve `IdentifierRef`
    /// on the way.
    fn find_symbol_by_ident_ref_ids(
        &mut self,
        hir: &UnresolvedHir,
        ident_ref_ids: &[IdentRefId],
    ) -> Option<SymbolId> {
        debug_assert!(!ident_ref_ids.is_empty());

        if ident_ref_ids.len() == 1 {
            todo!("Search for symbol in current scope, crawling up as needed")
        }

        fn extract_ident_and_span<'a>(
            resolver: &'a Resolver,
            hir: &'a UnresolvedHir,
            ident_ref_id: IdentRefId,
        ) -> (IdentId, &'a Span) {
            resolver
                .identifier_refs
                .get(ident_ref_id)
                .map(|ident_ref| (ident_ref.ident.id, &ident_ref.ident.span))
                .or_else(|| {
                    hir.identifier_refs
                        .get(ident_ref_id)
                        .map(|ident_ref| (ident_ref.ident.id, &ident_ref.ident.span))
                })
                .unwrap_or_else(|| {
                    panic!(
                        "{:?} neither found in self.identifier_refs={:?} nor in hir.identifier_refs={:?}",
                        ident_ref_id, resolver.identifier_refs, hir.identifier_refs
                    )
                })
        }

        fn build_visited_ident_string(resolver: &Resolver, ident_ids: &[IdentId]) -> String {
            ident_ids
                .iter()
                .map(|ident_id| resolver.identifiers.get_by_left(ident_id).unwrap().as_str())
                .collect::<Vec<_>>()
                .join(".")
        }

        let mut visited_ident_ids = Vec::<IdentId>::with_capacity(ident_ref_ids.len());

        let mut ns_symbols = self.symbols[*self.namespaces.root().unwrap()].as_namespace();
        for ident_ref_id in &ident_ref_ids[0..ident_ref_ids.len() - 1] {
            let (ident_id, span) = extract_ident_and_span(self, hir, *ident_ref_id);
            let symbols = ns_symbols.get(&ident_id).unwrap(); // {
            visited_ident_ids.push(ident_id);
            let symbols = symbols
                .iter()
                .map(|sid| &self.symbols[*sid])
                .filter(|s| matches!(s.kind, SymbolKind::Namespace(..)))
                .collect::<Vec<_>>();

            debug_assert!(symbols.len() <= 1, "{:?}", symbols);

            match symbols.first() {
                None => {
                    self.diagnostics.report_err(
                        format!(
                            "Symbol {sym} is not a namespace",
                            sym = build_visited_ident_string(self, &visited_ident_ids)
                        ),
                        span.clone(),
                        (file!(), line!()),
                    );
                    return None;
                }
                Some(symbol) => {
                    ns_symbols = symbol.as_namespace();
                }
            }
        }

        let (ident_id, span) = extract_ident_and_span(self, hir, *ident_ref_ids.last().unwrap());
        match ns_symbols.get(&ident_id) {
            None => {
                self.diagnostics.report_err(
                    format!(
                        "Symbol {sym} not found in {ns}",
                        sym = self.identifiers.get_by_left(&ident_id).unwrap(),
                        ns = build_visited_ident_string(self, &visited_ident_ids)
                    ),
                    span.clone(),
                    (file!(), line!()),
                );
                None
            }
            Some(symbols) => {
                debug_assert_eq!(symbols.len(), 1);
                symbols.first().cloned()
            }
        }
    }

    fn bring_namespace_symbols_into_scope(&mut self, namespace_symbol_id: SymbolId) {
        let namespace_symbols = self.symbols[namespace_symbol_id].as_namespace();

        for ident_id in namespace_symbols.keys() {
            for symbol_id in namespace_symbols.get(ident_id).unwrap() {
                self.scopes.push_symbol(*ident_id, *symbol_id)
            }
        }
    }

    fn bring_symbol_into_namespace(&mut self, ident_id: IdentId, symbol_id: SymbolId) {
        if let Some(namespace_symbol_id) = self.namespaces.last() {
            self.symbols
                .get_mut(*namespace_symbol_id)
                .unwrap()
                .as_namespace_mut()
                .entry(ident_id)
                .or_default()
                .push(symbol_id);
        }
    }
}

#[derive(Debug, Default)]
struct Scope {
    symbols: IdMap<IdentId, Vec<SymbolId>>,
}

#[derive(Debug, Default)]
struct Scopes {
    scopes: Stack<Scope>,
}

impl Scopes {
    fn len(&self) -> usize {
        self.scopes.len()
    }

    fn push(&mut self) {
        self.scopes.push_default();
    }

    fn pop(&mut self) {
        self.scopes.pop();
    }

    /// Returns the modifiable last scope. Returns `None` when the last scope does not exist.
    fn last_mut(&mut self) -> Option<&mut Scope> {
        self.scopes.last_mut()
    }

    /// Returns the modifiable symbols in the last scope. Returns `None` when the last scope does
    /// not exist.
    fn last_symbols_mut(&mut self) -> Option<&mut IdMap<IdentId, Vec<SymbolId>>> {
        self.scopes.last_mut().map(|scope| &mut scope.symbols)
    }

    /// Returns the symbols matching `ident_id` in the last scope. Returns and empty since when
    /// either no scope exists or when no symbol match `ident_id`.
    fn last_symbols_by_ident_id(&self, ident_id: IdentId) -> &[SymbolId] {
        self.scopes
            .last()
            .and_then(|scope| scope.symbols.get(&ident_id).map(|s| s.as_slice()))
            .unwrap_or_default()
    }

    /// Returns the modifiable symbols matching `ident_id` in the last scope. Returns `None` only
    /// when the last scope does not exist. I.e. when no symbol for `ident_id` already exist,
    /// returns and empty `Vec` ready to receive new symbols.
    fn last_symbols_mut_by_ident_id(&mut self, ident_id: IdentId) -> Option<&mut Vec<SymbolId>> {
        self.scopes
            .last_mut()
            .map(|scope| scope.symbols.entry(ident_id).or_default())
    }

    /// Adds a symbol to the last scope. Panics if no scopes exist.
    fn push_symbol(&mut self, ident_id: IdentId, symbol: SymbolId) {
        self.last_symbols_mut_by_ident_id(ident_id)
            .expect("current scope exists")
            .push(symbol);
    }

    fn clear_last(&mut self) {
        if let Some(last) = self.last_mut() {
            last.symbols.clear();
        }
    }

    fn iter(&self) -> Iter<'_, Scope> {
        self.scopes.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::bound::Bound;
    use crate::expression::Expression;
    use crate::identifier_ref::IdentifierRef;
    use crate::natives::Natives;
    use crate::statement::{Implementation, Statement, StatementKind};
    use crate::symbol::Symbol;
    use crate::typed::Typed;
    use crate::{ResolvedHir, UnresolvedHir};
    use insta::assert_debug_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;
    use transmute_nst::nodes::Nst;

    impl ResolvedHir {
        fn symbols_with_invalid_type(&self) -> Vec<&Symbol> {
            self.symbols
                .iter()
                .filter(|(id, _)| *id != crate::SymbolId::from(0))
                .map(|(_, symbol)| symbol)
                .filter(|symbol| symbol.type_id == crate::TypeId::from(0))
                .collect()
        }

        fn statements_with_invalid_type(&self) -> Vec<&Statement<Typed, Bound>> {
            self.statements
                .iter()
                .filter_map(|(_, stmt)| match &stmt.kind {
                    StatementKind::LetFn(_, _, params, ret, ..) => {
                        if ret.resolved_type_id() == crate::TypeId::from(0) {
                            return Some(stmt);
                        }
                        if params
                            .iter()
                            .any(|p| p.resolved_type_id() == crate::TypeId::from(0))
                        {
                            return Some(stmt);
                        }
                        None
                    }
                    StatementKind::Struct(_, _, _, Implementation::Provided(fields), _) => {
                        if fields
                            .iter()
                            .any(|f| f.resolved_type_id() == crate::TypeId::from(0))
                        {
                            Some(stmt)
                        } else {
                            None
                        }
                    }
                    _ => None,
                })
                .collect()
        }

        fn expressions_with_invalid_type(&self) -> Vec<&Expression<Typed>> {
            self.expressions
                .iter()
                .filter_map(|(_, expr)| {
                    if expr.resolved_type_id() == crate::TypeId::from(0) {
                        Some(expr)
                    } else {
                        None
                    }
                })
                .collect()
        }

        fn identifier_refs_with_unknown_binding(&self) -> Vec<&IdentifierRef<Bound>> {
            self.identifier_refs
                .iter()
                .filter_map(|(_, ident_ref)| {
                    if ident_ref.ident.resolved_symbol_id() == crate::SymbolId::from(0) {
                        Some(ident_ref)
                    } else {
                        None
                    }
                })
                .collect()
        }

        fn statements_with_unknown_binding(&self) -> Vec<&Statement<Typed, Bound>> {
            self.statements
                .iter()
                .filter_map(|(_, stmt)| match &stmt.kind {
                    StatementKind::Let(ident, _) => {
                        if ident.resolved_symbol_id() == crate::SymbolId::from(0) {
                            Some(stmt)
                        } else {
                            None
                        }
                    }
                    StatementKind::LetFn(ident, _, parameters, ..) => {
                        if ident.resolved_symbol_id() == crate::SymbolId::from(0) {
                            return Some(stmt);
                        }
                        if parameters
                            .iter()
                            .any(|p| p.resolved_symbol_id() == crate::SymbolId::from(0))
                        {
                            return Some(stmt);
                        }
                        None
                    }
                    StatementKind::Struct(ident, _, _, fields, _) => {
                        if ident.resolved_symbol_id() == crate::SymbolId::from(0) {
                            return Some(stmt);
                        }
                        match fields {
                            Implementation::Provided(fields) => {
                                if fields
                                    .iter()
                                    .any(|p| p.resolved_symbol_id() == crate::SymbolId::from(0))
                                {
                                    return Some(stmt);
                                }
                            }
                            Implementation::Native(_) => return None,
                        }
                        None
                    }
                    _ => None,
                })
                .collect()
        }
    }

    macro_rules! test_resolution {
        ($name:ident, $src:expr, $natives:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit = CompilationUnit::default();
                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), &format!("{}\nnamespace core {{}}", $src)),
                )
                .parse();

                let nst = Nst::from(compilation_unit.into_ast().unwrap());
                let resolved_hir = UnresolvedHir::from(nst).resolve($natives);

                if let Ok(hir) = &resolved_hir {
                    let symbols_with_invalid_type = hir.symbols_with_invalid_type();
                    assert!(
                        symbols_with_invalid_type.is_empty(),
                        "{symbols_with_invalid_type:?}"
                    );

                    let statements_with_invalid_types = hir.statements_with_invalid_type();
                    assert!(
                        statements_with_invalid_types.is_empty(),
                        "{statements_with_invalid_types:?}"
                    );

                    let expressions_with_invalid_types = hir.expressions_with_invalid_type();
                    assert!(
                        expressions_with_invalid_types.is_empty(),
                        "{expressions_with_invalid_types:?}"
                    );

                    let identifier_refs_with_unknown_binding =
                        hir.identifier_refs_with_unknown_binding();
                    assert!(
                        identifier_refs_with_unknown_binding.is_empty(),
                        "{identifier_refs_with_unknown_binding:?}"
                    );

                    let statements_refs_with_unknown_binding =
                        hir.statements_with_unknown_binding();
                    assert!(
                        statements_refs_with_unknown_binding.is_empty(),
                        "{statements_refs_with_unknown_binding:?}"
                    );
                }

                assert_debug_snapshot!(resolved_hir);
            }
        };
        ($name:ident, $src:expr) => {
            test_resolution!($name, $src, Natives::new());
        };
    }

    test_resolution!(
        resolve_ref_to_parameter,
        "let x(n: number): number = { n; }"
    );
    test_resolution!(resolve_ref_to_let, "let x(): number = { let n = 0; n; }");
    test_resolution!(resolve_ref_to_let_fn, "let x() = { } x();");
    test_resolution!(
        resolve_ref_to_parameter_nested,
        "let x(n: number): number = { while true { ret n; } }"
    );

    test_resolution!(resolve_missing_def, "let x() = { n; }");

    test_resolution!(rebinding, "let x = true; let x = 1; x + 1;");
    test_resolution!(
        fibonacci_rec,
        r#"
        let main(n: number): number {
            if n < 2 {
                ret n;
            }
            main(n - 1) + main(n - 2);
        }
        "#
    );

    test_resolution!(
        bindings_and_types,
        "struct S { f: S } let f(a: S, b: S): S { a; }",
        Natives::empty()
    );
    test_resolution!(
        annotation_function_bindings,
        "annotation a; @a let f() {}",
        Natives::empty()
    );
    test_resolution!(
        annotation_native_function_bindings,
        "namespace std { annotation native; } @std.native let f() {}",
        Natives::empty()
    );
    test_resolution!(
        annotation_struct_bindings,
        "annotation a; @a struct S {}",
        Natives::empty()
    );
    test_resolution!(
        annotation_native_struct_bindings,
        "namespace std { annotation native; } @std.native struct S {}",
        Natives::empty()
    );
    test_resolution!(basic_fn, "let f(){}", Natives::empty());
    test_resolution!(
        basic_fn_in_namespace,
        "namespace ns { let f() {} }",
        Natives::empty()
    );

    test_resolution!(
        let_expr_type_is_void,
        "let x = if true { ret 42; } else { ret 43; };"
    );

    test_resolution!(if_expected_boolean_condition_got_number, "if 42 {}");
    test_resolution!(if_expected_boolean_condition_got_boolean, "if true {}");
    test_resolution!(
        if_expected_boolean_condition_got_number_expr_binary,
        "if 40 + 2 {}"
    );
    test_resolution!(
        if_expected_boolean_condition_got_number_expr_unary,
        "if - 42 {}"
    );
    test_resolution!(
        if_expected_boolean_condition_got_no_type,
        "if if true { ret 42; } else { ret 43; } {}"
    );
    test_resolution!(
        if_expected_boolean_condition_got_boolean_expr,
        "if 42 > 40 {}"
    );
    test_resolution!(
        if_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; if forty_two {}"
    );
    test_resolution!(
        if_expected_boolean_condition_got_boolean_identifier,
        "let t = true; if t {}"
    );
    test_resolution!(if_mismatch_branch_types, "if true { true; } else { 42; }");
    test_resolution!(if_no_false_branch_to_val, "let n = 0; n = if true { 42; };");
    test_resolution!(
        if_false_branch_returns_to_val,
        r#"
            let f(): boolean = {
                let n = 0;
                n = if true {
                    42;
                } else {
                    ret false;
                };
                ret 42 == n;
            };
        "#
    );
    test_resolution!(
        if_true_branch_returns_to_val,
        r#"
            let f(): boolean = {
                let n = 0;
                n = if true {
                    ret false;
                } else {
                    42;
                };
                ret 42 == n;
            };
        "#
    );
    test_resolution!(if_no_false_branch, "if true { 42; }");
    test_resolution!(if_type, "let n = 0 + if true { 42; } else { 0; };");
    test_resolution!(
        if_expected_boolean_condition_got_number_in_else_if,
        "if true {} else if 42 {}"
    );
    test_resolution!(if_type_of_else_if, "if true { 42; } else if false { 0; }");
    test_resolution!(while_expected_boolean_condition_got_number, "while 42 {}");
    test_resolution!(
        while_expected_boolean_condition_got_no_type,
        "while if true { ret 42; } else { ret 43; } {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_boolean,
        "while true {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_number_expr_binary,
        "while 40 + 2 {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_number_expr_unary,
        "while - 42 {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_boolean_expr,
        "while 42 > 40 {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; while forty_two {}"
    );
    test_resolution!(
        while_expected_boolean_condition_got_boolean_identifier,
        "let t = true; while t {}"
    );
    test_resolution!(
        assignment_wrong_type,
        "let forty_two = 42; forty_two = true;"
    );
    test_resolution!(
        assignment_correct_type,
        "let forty_two = 0; forty_two = 42;"
    );
    test_resolution!(
        assignment_to_function_parameter_correct_type,
        "let f(n: number): number = { n = 1; }"
    );
    test_resolution!(
        assignment_to_function_parameter_incorrect_type,
        "let f(n: number): number = { n = true; }"
    );
    test_resolution!(
        assignment_wrong_type_from_function,
        "let forty_two = 42; let f(): boolean = true; forty_two = f();"
    );
    test_resolution!(
        assignment_wrong_type_from_void_function,
        "let forty_two = 42; let f() = {} forty_two = f();"
    );
    test_resolution!(
        assignment_always_returning_expr,
        "let forty_two = 42; forty_two = if true { ret 42; } else { ret 43; };"
    );
    test_resolution!(
        assignment_correct_type_from_function,
        "let forty_two = 0; let f(): number = 42; forty_two = f();"
    );
    test_resolution!(function_is_allowed_to_return_void, "let f() = { 1; }");
    test_resolution!(function_has_struct_params, "struct S {} let f(s: S) = { }");
    test_resolution!(
        struct_instantiation,
        "struct S { x: number } let s = S { x: 1 };"
    );
    test_resolution!(
        function_returns_struct,
        "struct S {} let f(): S = { S { }; }"
    );
    test_resolution!(
        function_returns_struct_field,
        "struct S { field: number } let f(s: S): number = { s.field; }"
    );
    test_resolution!(
        access_struct_field_read,
        "struct S { field: boolean } let s = S { field: true }; if s.field { }"
    );
    test_resolution!(
        access_struct_field_nested_read,
        r#"
        struct S1 { s: S2 }
        struct S2 { f: boolean }
        let s = S1 {
            s: S2 {
                f: true
            }
        };
        if s.s.f { }
        "#
    );

    test_resolution!(
        if_evaluates_to_struct,
        r#"
        struct S { f: number }

        let a = S { f: 1 };
        let b = S { f: 2 };

        if 1 == 1 {
            a;
        } else {
            b;
        }.f = 42;
        "#
    );
    test_resolution!(
        access_struct_field_read_invalid_type,
        "struct S { field: number } let s = S { field: 1 }; if s.field { }"
    );
    test_resolution!(
        access_struct_field_write,
        "struct S { field: number } let s = S { field: 1 }; s.field = 1;"
    );
    test_resolution!(
        access_struct_field_write_wrong_type,
        "struct S { field: number } let s = S { field: 1 }; s.field = false;"
    );
    test_resolution!(
        function_returns_void_but_expect_struct,
        "struct S {} let f(): S = { }"
    );
    test_resolution!(struct_unknown, "let s = S {};");
    test_resolution!(struct_length, "struct S { x: number } let s = S { };");
    test_resolution!(duplicate_struct_field, "struct S { x: number, x: number }");
    test_resolution!(
        struct_invalid_field_type,
        "struct S { x: number } let s = S { x: 1 == 1 };"
    );
    test_resolution!(access_non_struct, "1.x;");
    test_resolution!(access_namespace, "namespace a {} a.x;");
    test_resolution!(
        access_non_namespace_then_non_namespace,
        "struct S {} @S.x let f() {}"
    );
    test_resolution!(
        access_namespace_then_non_namespace,
        "namespace a { struct S {} } @a.S.x let f() {}"
    );
    test_resolution!(
        access_namespace_then_non_namespace_then_non_namespace,
        "namespace a { struct S {} } @a.S.x.y let f() {}"
    );
    test_resolution!(
        access_struct_unknown_field,
        "struct S {} let a = S {}; a.x;"
    );
    test_resolution!(function_void_cannot_return_number, "let f() = { ret 1; }");
    test_resolution!(function_invalid_return_type, "let f(): unknown = { }");
    test_resolution!(
        function_wrong_return_type,
        "let f(): boolean = { true; 42; }"
    );
    test_resolution!(function_wrong_return_type_2, "let f(): boolean = { }");
    test_resolution!(
        function_wrong_early_return_type,
        "let f(): number = { if false { ret false; } 42; }"
    );
    test_resolution!(
        function_parameter_returned_correct_type,
        "let f(n: number): number = { n; }"
    );
    test_resolution!(
        function_parameter_returned_wrong_type,
        "let f(n: number): boolean = { n; }"
    );
    test_resolution!(
        function_parameter_invalid_type,
        "let f(n: unknown) = { let a = n + true; }"
    );
    test_resolution!(
        function_parameter_incorrect_type,
        "let f(n: number) = { let a = n + true; }"
    );
    test_resolution!(
        function_parameter_incorrect_arity,
        "let f(n: number, b: boolean) = { f(0); }"
    );
    test_resolution!(
        duplicate_function_parameter_name,
        "let f(n: number, n: number) = { }"
    );
    test_resolution!(function_not_found, "let f() = { g(); }");
    test_resolution!(
        function_invalid_return_type_after_valid_return_type,
        "let f(n: number): number = { ret 41; ret true; }"
    );
    test_resolution!(unary_operator_invalid_type, "let n = - true;");
    test_resolution!(
        unary_operator_no_type,
        "let n = - if true { ret 42; } else { ret 43; };"
    );
    test_resolution!(call_variable, "let n = 10; n();");
    test_resolution!(
        unreachable_statement1,
        r#"
        let f(n: number): number = {
            if n == 42 {
                let m = 0;
                ret m + 1;
            } else {
                let m = 0;
                ret m - 1;
            };
            ret f(42);
        }
        "#
    );
    test_resolution!(
        unreachable_statement3,
        r#"
        let f(n: number): number = {
            while n != 42 {
                ret n;
            }
            ret n;
        }
        "#
    );
    test_resolution!(
        unreachable_statement2,
        r#"
        let f(n: number): number = {
            if n == 42 {
                let m = 0;
                ret m + 1;
            } else {
                let m = 0;
                ret m - 1;
            };
            ret 42;
        }
        "#
    );
    test_resolution!(nested_function_same_type, "let f() { let g() {} }");
    test_resolution!(
        nested_function_different_types,
        "let f(): number { let g(): boolean { true; }; 1; }"
    );

    test_resolution!(
        struct_same_field_name,
        r#"
        struct Inner { field: number };
        struct Outer { field: number };
        "#
    );
    test_resolution!(
        struct_instantiation_same_field_name,
        r#"
        struct Inner { field: number };
        struct Outer { field: Inner };
        let s = Outer { field: Inner { field: 1 } };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameter,
        r#"
        struct Struct<T> { field: T };
        let s = Struct!<number> { field: 1 };
        "#
    );
    test_resolution!(
        struct_instantiation_missing_type_parameter,
        r#"
        struct Struct<T> { field: T };
        let s = Struct { field: 1 };
        "#
    );

    test_resolution!(void_function_explicit_void_ret, "let f() { ret; }");
    test_resolution!(void_function_implicit_void_ret, "let f() { }");
    test_resolution!(void_function_implicit_number_ret, "let f() { 1; }");
    test_resolution!(
        non_void_function_explicit_void_ret,
        r#"let f(): number { ret; }"#
    );
    test_resolution!(non_void_function_implicit_void_ret, "let f(): number { }");

    test_resolution!(let_from_void, "let g() {} let f() { let a = g(); }");

    test_resolution!(return_from_void, "let g() {} let f(): number { g(); }");

    test_resolution!(
        struct_in_function,
        r#"
        let f() {
            struct S {
                field: number
            }
            let s = S {
                field: 1
            };
        }
        "#
    );
    test_resolution!(
        structs_in_functions,
        r#"
        let f() {
            struct Sf {
                field: number
            }
        }
        let g() {
            struct Sg {
                field: number
            }
        }
        "#
    );
    test_resolution!(
        struct_assignment,
        r#"
        struct S {
            field: number
        }
        let f() {
            let s = S { field: 1 };
            s.field = 2;
        }
        "#
    );
    test_resolution!(
        struct_assignment_wrong_type,
        r#"
        struct S {
            field: number
        }
        let f() {
            let s = S { field: 1 };
            s.field = false;
        }
        "#
    );

    test_resolution!(
        array_homogenous_types,
        r#"
        let f() {
            let a = [0, 1];
        }
        "#
    );
    test_resolution!(
        array_return_type,
        r#"
        let f(): [number; 2] {
            [0, 1];
        }
        "#
    );
    test_resolution!(
        array_return_type_wrong_len,
        r#"
        let f(): [number; 2] {
            [0, 1, 2];
        }
        "#
    );
    test_resolution!(
        array_return_type_wrong_base_typee,
        r#"
        let f(): [number; 2] {
            [true, false];
        }
        "#
    );
    test_resolution!(
        array_parameter_type,
        r#"
        let f(a: [number; 2]) {
        }
        let g() {
            f([1, 2]);
        }
        "#
    );
    test_resolution!(
        array_of_structs,
        r#"
        struct S { field: number }
        let f() {
            let a = [
                S { field: 1 },
                S { field: 2 },
            ];
        }
        "#
    );
    test_resolution!(
        struct_of_array,
        r#"
        struct S {
            field: [number; 2]
        }
        let f() {
            let a = [
                S { field: [0, 1] },
                S { field: [2, 3] },
            ];
        }
        "#
    );
    test_resolution!(array_heterogeneous_types, "let f() { let a = [0, false]; }");
    test_resolution!(
        array_type_1,
        "let f() { if true { [0, 1]; } else { [2, 3, 4]; } }"
    );
    // todo:ux we must have the inner type name in the error (this has to do with the Display impl.
    //   of Type
    test_resolution!(
        array_type_2,
        "let f() { if true { [0, 1]; } else { [true, false]; } }"
    );
    test_resolution!(array_access, "let f() { let a = [0]; a[0]; }");
    test_resolution!(array_write_access, "let f() { let a = [0]; a[0] = 1; }");
    test_resolution!(
        array_write_access_wrong_type,
        "let f() { let a = [0]; a[0] = false; }"
    );
    test_resolution!(array_instantiation_and_access, "let f() { [0, 1][0]; }");
    test_resolution!(array_access_not_array, "let f() { let a = 1; a[0]; }");
    test_resolution!(
        array_access_not_numeric_index,
        "let f() { let a = [0]; a[true]; }"
    );
    test_resolution!(
        array_return_wrong_length,
        "let f(): [number; 1] { [0, 1]; }"
    );
    test_resolution!(
        array_parameter_wrong_length,
        r#"
        let f(a: [number; 2]) {
        }
        let g() {
            f([1, 2, 3]);
        }
        "#
    );
    test_resolution!(define_annotation, "annotation a;");
    test_resolution!(
        native_function_have_no_body,
        r#"
        namespace std { annotation native; }
        @std.native let f(): number { }
        "#
    );
    test_resolution!(
        native_function_must_not_have_body,
        r#"
        namespace std { annotation native; }
        @std.native let f(): number { true; }
        "#
    );
    test_resolution!(
        non_native_function_have_body,
        r#"
        annotation non_native;
        @non_native let f(): core.number { 10; }
        "#
    );
    test_resolution!(
        native_struct_have_no_body,
        r#"
        annotation native;
        @native struct S {}
        "#
    );
    test_resolution!(
        native_struct_must_not_have_body,
        r#"
        namespace std {annotation native; }
        @std.native struct S { field1: number, field2: number }
        "#
    );
    test_resolution!(
        native_struct_cannot_be_instantiated,
        r#"
        namespace std { annotation native; }
        @std.native struct S {  }
        let f() {
            let s = S {};
        }
        "#
    );
    test_resolution!(
        native_struct_fields_cannot_be_accessed,
        r#"
        namespace std { annotation native; }
        @std.native struct S {  }
        let f(s: S) {
            s.whatever;
        }
        "#
    );
    test_resolution!(
        non_native_struct_have_body,
        r#"
        annotation non_native;
        @non_native struct S { field: number }
        "#
    );
    test_resolution!(
        unknown_function_annotation,
        r#"
        @unknown let f(): number { 10; }
        "#
    );
    test_resolution!(
        unknown_struct_annotation,
        r#"
        @unknown struct S {}
        "#
    );
    test_resolution!(
        void_in_arrays,
        r#"
        let main() { let a = [ f() ]; }
        let f() {}
        "#
    );
    test_resolution!(
        native_struct_can_be_used,
        r#"
        annotation native;
        namespace std {
            namespace str {
                @native struct string {}
            }
        }
        @native let print(s: std.str.string) {}
        let main() {
            let hello = "hello";
            print(hello);
        }
        "#
    );
    test_resolution!(
        namespace,
        r#"
        namespace ns {
            let f1(): number { 1; }
        }
        let f2() {
            1 + ns.f1();
        }
        "#
    );
    test_resolution!(
        nested_type,
        r#"
        namespace std {
            struct S {}
        }
        namespace user {
            let f(in: std.S) {}
        }
        "#
    );
    test_resolution!(
        mutually_referenced_functions,
        r#"
        namespace a {
            let fa() { b.fb(); }
        }
        namespace b {
            let fb() { a.fa(); }
        }
        "#
    );
    test_resolution!(
        mutually_referenced_structs_in_function,
        r#"
        namespace a {
            let fa(b: b.B) {}
            struct A {}
        }
        namespace b {
            let fb(a: a.A) {}
            struct B {}
        }
        "#
    );
    test_resolution!(
        mutually_referenced_structs_in_structs,
        r#"
        namespace a {
            struct A {
              f: b.B
            }
        }
        namespace b {
            struct B {
              f: a.A
            }
        }
        "#
    );

    test_resolution!(
        access_unqualified_function,
        r#"
        namespace a {
            let f() {}
        }
        let main() {
            f();
        }
        "#
    );
    test_resolution!(
        access_unqualified_function_same_namespace,
        r#"
        namespace a {
            let f() {}
            let g() {
                f();
            }
        }
        "#
    );
    test_resolution!(
        access_unqualified_function_recursive,
        r#"
        namespace a {
            let f() {
                f();
            }
        }
        "#
    );
    test_resolution!(
        access_unqualified_function_noot_namespace,
        r#"
        let f() {
            f();
        }
        let g() {
            f();
        }
        "#
    );

    test_resolution!(
        access_unqualified_struct,
        r#"
        namespace a {
            struct S {}
        }
        let f(s: S) {
        }
        "#
    );
    test_resolution!(
        access_unqualified_struct_same_namespace,
        r#"
        namespace a {
            struct S {}
            let f(s: S) {
            }
        }
        "#
    );
    test_resolution!(
        access_unqualified_struct_root_namespace,
        r#"
        struct S {}
        let f(s: S) {
        }
        "#
    );

    test_resolution!(
        access_unqualified_annotation,
        r#"
        namespace a {
            annotation b;
        }
        @b
        let f() {
        }
        "#
    );
    test_resolution!(
        access_unqualified_annotation_same_namespace,
        r#"
        namespace a {
            annotation b;
            @b
            let f() {
            }
        }
        "#
    );
    test_resolution!(
        access_unqualified_annotation_root_namespace,
        r#"
        annotation b;
        @b
        let f() {
        }
        "#
    );

    test_resolution!(
        access_qualified_function,
        r#"
        namespace a {
            let f() {}
        }
        let f() {
            a.f();
        }
        "#
    );
    test_resolution!(
        access_qualified_function_recursive,
        r#"
        namespace a {
            let f() {
                a.f();
            }
        }
        "#
    );
    test_resolution!(
        access_qualified_struct,
        r#"
        namespace a {
            struct S {}
        }
        let f(s: a.S) {
        }
        "#
    );
    test_resolution!(
        access_qualified_annotation,
        r#"
        namespace a {
            annotation b;
        }
        @a.b
        let f() {
        }
        "#
    );
    test_resolution!(
        access_core,
        r#"
        namespace a {
            let f(n: number) {}
            let g(n: core.number) {}
        }
        let h(n: number) {}
        let i(n: core.number) {}
        "#
    );

    test_resolution!(
        symbols_not_found,
        r#"
        namespace a {
            namespace b {
                struct C {}
            }
        }
        let f1(): a.C {}
        let f2(): a.b.D {}
        "#
    );

    test_resolution!(
        type_expected,
        r#"
        namespace a {}
        let f(): a {}
        "#
    );

    test_resolution!(
        types_in_nested_namespace,
        r#"
        namespace std {
            namespace list {
                struct List {}
            }
            namespace env {
                let f(p: std.list.List) {}
            }
        }
        "#
    );

    // todo:test align with is_symbol_in_current_scope (and see todo there as well)
    test_resolution!(
        duplicate_function_definition,
        r#"
        let f () {}
        let f () {}
        "#
    );
    test_resolution!(
        duplicate_struct_definition,
        r#"
        struct S {}
        struct S {}
        "#
    );

    test_resolution!(
        struct_same_name,
        r#"
        namespace ns1 {
            struct S {}
            namespace ns2 {
                struct S {}
            }
        }
        "#
    );
    test_resolution!(
        fn_same_name,
        r#"
        namespace ns1 {
            let f() {}
            namespace ns2 {
                let f() {}
            }
        }
        "#
    );

    test_resolution!(
        use_struct_target_exists,
        r#"
        namespace ns1 {
            struct S {}
        }
        namespace ns2 {
            use ns1.S;
            let f(s: S) {}
        }
        "#
    );
    test_resolution!(
        use_function_target_exists,
        r#"
        namespace ns1 {
            let f() {}
        }
        namespace ns2 {
            use ns1.f;
            let g() {
                f();
            }
        }
        "#
    );
    test_resolution!(
        use_function_in_function_target_exists,
        r#"
        namespace ns1 {
            let f() {}
        }
        namespace ns2 {
            let g() {
                use ns1.f;
                f();
            }
        }
        "#
    );
    test_resolution!(
        use_target_does_not_exist_in_namespace,
        r#"
        namespace ns1 {}
        namespace ns2 {
            use ns1.S;
            let f(s: S) {}
        }
        "#
    );
    test_resolution!(
        use_target_namespace_does_not_exist,
        r#"
        namespace ns2 {
            use ns1.S;
            let f(s: S) {}
        }
        "#
    );
    test_resolution!(
        namespace_is_invalid_in_block,
        r#"
        let f() {
            namespace a {
            }
        }
        "#
    );

    test_resolution!(
        function_call_on_value,
        r#"
        let print(n: number) {}
        let f() {
            1.print();
        }
        "#
    );
    test_resolution!(
        function_call_on_string,
        r#"
        let f() {
            "str".print();
        }
        namespace std {
            annotation native;
            namespace str {
                @std.native
                struct string {}
                let print(n: string) {}
            }
        }
        "#
    );
    test_resolution!(
        function_call_on_struct,
        r#"
        let f() {
            S{}.print();
        }
        struct S {}
        let print(n: S) {}
        "#
    );
    test_resolution!(
        unknown_function_call_on_struct,
        r#"
        let f() {
            S{}.print();
        }
        struct S {}
        "#
    );
}
