use crate::natives::{Native, Natives, Type};
use crate::nodes::{
    Annotation, ExitPoint, Implementation, RetMode, Statement, StatementKind, Target, TypeDefKind,
};
use crate::symbol::{Symbol, SymbolKind};
use crate::{As, ExpressionKind, Literal, LiteralKind};
use crate::{
    FindSymbol, Hir, IntoBound, IntoBoundTyped, IntoTyped, RequiredSymbolKind, TryAsLiteral,
};
use bimap::BiHashMap;
use std::collections::{HashMap, HashSet};
use std::mem;
use transmute_core::error::Diagnostics;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::span::Span;
use transmute_core::stack::{Iter, Stack};
use transmute_core::vec_map::VecMap;
use transmute_nst::nodes::{Nst, StatementKind as NstStatementKind};

static NATIVE_ANNOTATION: [&str; 2] = ["std", "native"];

// todo:refactoring each `resolve_` method does the actual resolution instead of giving to its
//  caller the information required to resolve
// todo:refactoring (linked to previous) should the resolve_* function really return something?

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
    types: BiHashMap<TypeId, Type>,
    types_by_name: HashMap<&'static str, TypeId>,
    symbols: VecMap<SymbolId, Symbol>,
    not_found_symbol_id: SymbolId,

    /// Maps a statement to its parent
    parent: HashMap<StmtId, StmtId>,

    // todo why a Vec<SymbolId>?
    /// Maps an `IdentifierRef` (by their`IdentifierRefId`) to `SymbolId`s.
    identifier_ref_bindings: HashMap<IdentRefId, Vec<SymbolId>>,

    /// Maps an `Expression` (from the `ExprId`) to a `TypeId`.
    expression_types: HashMap<ExprId, TypeId>,

    /// Maps a `Parameter` (from the `StmtId` where it's defined and its index in the list) to a
    /// `SymbolId`.
    parameter_bindings: HashMap<(StmtId, usize), (SymbolId, TypeId)>,

    /// Maps a `Field` (from the `StmtId` where it's defined and its index in the list) to a
    /// `SymbolId`.
    field_bindings: HashMap<(StmtId, usize), (SymbolId, TypeId)>,

    /// Maps a `Let` statement's `Identifier` to a `SymbolId`.
    let_bindings: HashMap<StmtId, SymbolId>,

    /// Maps a `LetFn` statement's `Identifier` to a `SymbolId`.
    fn_bindings: HashMap<StmtId, SymbolId>,

    /// Maps a `LetFn` statement's return type to a `TypeId`.
    fn_return_types: HashMap<StmtId, TypeId>,

    /// Maps a `Struct` statement's `Identifier` to a `SymbolId` (the boolean is used to tell
    /// whether the struct was inserted only (`false`) or also resolved (`true`).
    struct_bindings: HashMap<StmtId, (SymbolId, bool)>,

    /// Maps a `Namespace` statement's `Identifier` to a `SymbolId`.
    namespace_bindings: HashMap<StmtId, SymbolId>,

    /// Maps a `Annotation` statement's `Identifier` to a `SymbolId`.
    annotation_bindings: HashMap<StmtId, SymbolId>,

    /// Tells whether a symbol is a native symbol.
    native_symbols: HashSet<SymbolId>,

    // work
    namespace_stack: Stack<SymbolId>,
    scopes: Scopes,
    fn_stack: Stack<StmtId>,

    /// maps `TypeId`s to functions
    type_functions: HashMap<TypeId, HashMap<IdentId, SymbolId>>,
    type_parameters: HashMap<(StmtId, usize), TypeId>,

    diagnostics: Diagnostics<()>,
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            identifiers: Default::default(),
            types: Default::default(),
            types_by_name: Default::default(),
            symbols: Default::default(),
            not_found_symbol_id: Default::default(),

            parent: Default::default(),
            identifier_ref_bindings: Default::default(),
            expression_types: Default::default(),
            parameter_bindings: Default::default(),
            field_bindings: Default::default(),
            let_bindings: Default::default(),
            fn_bindings: Default::default(),
            fn_return_types: Default::default(),
            struct_bindings: Default::default(),
            namespace_bindings: Default::default(),
            annotation_bindings: Default::default(),

            native_symbols: Default::default(),
            namespace_stack: Default::default(),
            scopes: Default::default(),
            fn_stack: Default::default(),

            type_functions: Default::default(),
            type_parameters: Default::default(),

            diagnostics: Default::default(),
        }
    }

    pub fn resolve(mut self, natives: Natives, mut nst: Nst) -> Result<Hir, Diagnostics<()>> {
        let root = nst.root;

        // init. identifiers
        self.identifiers = BiHashMap::from_iter(mem::take(&mut nst.identifiers));

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

        // init. types
        // debug_assert!(nst.types.is_empty());
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
        let root_root_namespace_symbol_id = self.insert_namespace(&nst, root);
        self.namespace_stack.push(root_root_namespace_symbol_id);
        debug_assert_eq!(self.namespace_stack.len(), 1, "{:?}", &self.namespace_stack);

        // STEP 2 ----------------------------------------------------------------------------------
        let core_namespace_ident_id = *self.identifiers.get_by_right("core").unwrap();
        let core_namespace_symbol_id = self.symbols[*self.namespace_stack.root().unwrap()]
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

        debug_assert_eq!(self.namespace_stack.len(), 1, "{:?}", &self.namespace_stack);
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
        debug_assert_eq!(self.namespace_stack.len(), 1, "{:?}", &self.namespace_stack);

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
        debug_assert_eq!(self.scopes.len(), 1, "{:?}", self.namespace_stack);
        self.insert_namespace_functions(&nst, root);
        debug_assert_eq!(self.scopes.len(), 1, "{:?}", self.namespace_stack);

        // STEP 5 ----------------------------------------------------------------------------------
        // insert root namespace's fn symbols into the first scope
        // todo:refactoring try to use bring_namespace_symbols_into_scope
        let root_scope = self.scopes.last_symbols_mut().unwrap();
        let root_symbols = self.symbols[*self.namespace_stack.root().unwrap()].as_namespace();
        for ident_id in root_symbols.keys() {
            for symbol_id in root_symbols.get(ident_id).unwrap() {
                if matches!(self.symbols[*symbol_id].kind, SymbolKind::LetFn(..)) {
                    root_scope.entry(*ident_id).or_default().push(*symbol_id);
                }
            }
        }

        // STEP 6 ----------------------------------------------------------------------------------
        debug_assert_eq!(self.namespace_stack.len(), 1, "{:?}", self.namespace_stack);
        self.resolve_statement(&nst, root);
        debug_assert_eq!(self.namespace_stack.len(), 1, "{:?}", self.namespace_stack);

        if !self.diagnostics.is_empty() {
            return Err(self.diagnostics);
        }

        let types = VecMap::from_iter(self.types);

        let identifier_refs = nst
            .identifier_refs
            .into_iter()
            .map(|(ident_ref_id, ident_ref)| {
                let bindings = self
                    .identifier_ref_bindings
                    .remove(&ident_ref_id)
                    .unwrap_or_else(|| {
                        panic!(
                            "{ident_ref_id:?} ({:?}) is bound",
                            self.identifiers.get_by_left(&ident_ref.ident.id)
                        )
                    });
                debug_assert_eq!(bindings.len(), 1);
                (ident_ref_id, ident_ref.into_bound(bindings[0]))
            })
            .collect::<VecMap<_, _>>();

        let expressions = nst
            .expressions
            .into_iter()
            .map(|(expr_id, expression)| {
                (
                    expr_id,
                    expression.into_typed(
                        self.expression_types
                            .remove(&expr_id)
                            .expect("expression is typed"),
                    ),
                )
            })
            .collect::<VecMap<_, _>>();

        let statements = nst
            .statements
            .into_iter()
            .map(|(stmt_id, stmt)| {
                (
                    stmt_id,
                    match stmt.kind {
                        NstStatementKind::Expression(expr_id) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Expression(expr_id),
                            span: stmt.span,
                        },
                        NstStatementKind::Let(ident, expr_id) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Let(
                                ident.into_bound(
                                    self.let_bindings.remove(&stmt_id).expect("was bound"),
                                ),
                                expr_id,
                            ),
                            span: stmt.span,
                        },
                        NstStatementKind::Ret(expr_id, ret_mode) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Ret(expr_id, ret_mode),
                            span: stmt.span,
                        },
                        NstStatementKind::LetFn(ident, annotations, parameters, ret, expr_id) => {
                            let symbol_id = self
                                .fn_bindings
                                .remove(&stmt_id)
                                .unwrap_or_else(|| panic!("{stmt_id:?} was bound"));

                            let implementation = if self.native_symbols.contains(&symbol_id) {
                                #[cfg(not(debug_assertions))]
                                {
                                    Implementation::Native
                                }
                                #[cfg(debug_assertions)]
                                {
                                    // because the implicit ret runs before the resolution, empty function
                                    // bodies actually have exactly one implicit ret none.
                                    Implementation::Native(expr_id)
                                }
                            } else {
                                Implementation::Provided(expr_id)
                            };

                            Statement {
                                id: stmt_id,
                                kind: StatementKind::LetFn(
                                    ident.into_bound(
                                        self.let_bindings.remove(&stmt_id).expect("was bound"),
                                    ),
                                    annotations,
                                    parameters
                                        .into_iter()
                                        .enumerate()
                                        .map(|(index, parameter)| {
                                            let (symbol_id, type_id) = self
                                                .parameter_bindings
                                                .remove(&(stmt_id, index))
                                                .expect("was bound");
                                            parameter.into_bound_typed(symbol_id, type_id)
                                        })
                                        .collect(),
                                    ret.into_typed(
                                        self.fn_return_types.remove(&stmt_id).expect("was typed"),
                                    ),
                                    implementation,
                                    self.parent.remove(&stmt_id),
                                ),
                                span: stmt.span,
                            }
                        }
                        NstStatementKind::Struct(ident, annotations, _, fields) => {
                            let symbol_id = self
                                .struct_bindings
                                .remove(&stmt_id)
                                .unwrap_or_else(|| panic!("{stmt_id:?} was bound"))
                                .0;
                            let implementation = if self.native_symbols.contains(&symbol_id) {
                                #[cfg(not(debug_assertions))]
                                {
                                    Implementation::Native
                                }
                                #[cfg(debug_assertions)]
                                {
                                    Implementation::Native(vec![])
                                }
                            } else {
                                Implementation::Provided(
                                    fields
                                        .into_iter()
                                        .enumerate()
                                        .map(|(index, field)| {
                                            let (symbol_id, type_id) = self
                                                .field_bindings
                                                .remove(&(stmt_id, index))
                                                .expect("was bound");
                                            field.into_bound_typed(symbol_id, type_id)
                                        })
                                        .collect(),
                                )
                            };

                            Statement {
                                id: stmt_id,
                                kind: StatementKind::Struct(
                                    ident.into_bound(symbol_id),
                                    annotations,
                                    implementation,
                                    self.parent.remove(&stmt_id),
                                ),
                                span: stmt.span,
                            }
                        }
                        NstStatementKind::Annotation(ident) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Annotation(
                                ident.into_bound(
                                    self.annotation_bindings
                                        .remove(&stmt_id)
                                        .expect("was bound"),
                                ),
                            ),
                            span: stmt.span,
                        },
                        NstStatementKind::Use(ident_ref_ids) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Use(ident_ref_ids),
                            span: stmt.span,
                        },
                        NstStatementKind::Namespace(ident, input, stmt_ids) => Statement {
                            id: stmt_id,
                            kind: StatementKind::Namespace(
                                ident.into_bound(
                                    self.namespace_bindings.remove(&stmt_id).expect("was bound"),
                                ),
                                input,
                                stmt_ids,
                            ),
                            span: stmt.span,
                        },
                    },
                )
            })
            .collect::<VecMap<_, _>>();

        // todo:test try to find a way to keep all the statements, including the
        //  `StatementKind::Use` ones, as well as all the related ident_refs (that may have more
        //  than one binding) for the test / dump during tests
        let use_stmts = statements
            .iter()
            .filter(|(_, stmt)| matches!(stmt.kind, StatementKind::Use(..)))
            .map(|(id, _)| id)
            .collect::<Vec<_>>();

        Ok(Hir {
            identifiers: VecMap::from_iter(self.identifiers),
            identifier_refs,
            // we remove all references to Use statements
            expressions: expressions
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
            statements: statements
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
            type_defs: nst.type_defs,
            root: nst.root,
            symbols: self.symbols,
            types,
            exit_points: nst.exit_points,
        })
    }

    fn resolve_expression(&mut self, nst: &Nst, expr_id: ExprId) -> (TypeId, Option<SymbolId>) {
        if let Some(type_id) = self.expression_types.get(&expr_id) {
            let symbol_id_id = nst.expressions[expr_id]
                .try_as_literal()
                .and_then(|lit| match &lit.kind {
                    LiteralKind::Identifier(ident_ref_id) => Some(*ident_ref_id),
                    _ => None,
                })
                // todo:refactoring can we get rid of clone()
                .map(|ident_ref_id| {
                    self.identifier_ref_bindings
                        .get(&ident_ref_id)
                        .expect("was bound")
                        .clone()
                })
                .map(|symbol_ids| {
                    // the expectation is that if the expression has a type, the potential
                    // identifier it is, is also bound
                    assert_eq!(symbol_ids.len(), 1);
                    symbol_ids[0]
                });
            return (*type_id, symbol_id_id);
        }

        let expr = &nst.expressions[expr_id];
        let (type_id, symbol_id) = match &expr.kind {
            ExpressionKind::Assignment(Target::Direct(ident_ref), expr) => {
                (self.resolve_direct_assignment(nst, *ident_ref, *expr), None)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                self.resolve_indirect_assignment(nst, lhs_expr_id, rhs_expr_id)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => (
                self.resolve_if(nst, *cond, *true_branch, *false_branch),
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
                LiteralKind::Identifier(ident_ref_id) => {
                    self.resolve_ident_ref(nst, ident_ref_id, RequiredSymbolKind::Other);
                    let symbol_ids = self
                        .identifier_ref_bindings
                        .get(&ident_ref_id)
                        .expect("was bound");

                    debug_assert!(symbol_ids.len() <= 1);
                    let type_id = symbol_ids
                        .first()
                        .map(|s| self.symbols[*s].type_id)
                        .unwrap_or(self.find_type_id_by_type(&Type::Invalid));

                    (type_id, symbol_ids.first().cloned())
                }
            },
            ExpressionKind::Access(expr_id, ident_ref_id) => self.resolve_access(
                nst,
                &expr.span,
                *expr_id,
                *ident_ref_id,
                RequiredSymbolKind::Other,
            ),
            ExpressionKind::FunctionCall(expr_id, params) => (
                self.resolve_function_call(nst, *expr_id, params.clone().as_slice()),
                None,
            ),
            ExpressionKind::While(cond, expr) => self.resolve_while(nst, *cond, *expr),
            ExpressionKind::Block(stmts) => (self.resolve_block(nst, &stmts.clone()), None),
            ExpressionKind::StructInstantiation(ident_ref_id, type_parameters, fields) => (
                self.resolve_struct_instantiation(
                    nst,
                    *ident_ref_id,
                    type_parameters,
                    fields,
                    &expr.span,
                ),
                None,
            ),
            ExpressionKind::ArrayInstantiation(values) => {
                (self.resolve_array_instantiation(nst, values), None)
            }
            ExpressionKind::ArrayAccess(expr, index) => {
                (self.resolve_array_access(nst, *expr, *index), None)
            }
        };

        let type_id = self.find_type_parameter_actual_type_id(type_id);

        self.expression_types.insert(expr_id, type_id);

        (type_id, symbol_id)
    }

    fn resolve_direct_assignment(
        &mut self,
        nst: &Nst,
        ident_ref_id: IdentRefId,
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

        let rhs_type_id = self.resolve_expression(nst, expr).0;

        // todo:feature:fn-value to search for method, we need to extract the parameter types from the
        //  expr_type, if it corresponds to a function type. We don't have this
        //  information yet and thus we cannot assign to a variable holding a function
        //  (yet).
        self.resolve_ident_ref(nst, ident_ref_id, RequiredSymbolKind::Other);
        let lhs_symbol_ids = self
            .identifier_ref_bindings
            .get(&ident_ref_id)
            .expect("was bound");
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
            // todo:ux better error message (see test
            //  struct_instantiation_with_type_parameters_reassign_invalid_type)
            self.diagnostics.report_err(
                format!(
                    "RHS expected to be of type {}, got {}",
                    self.find_type_by_type_id(lhs_type_id),
                    self.find_type_by_type_id(rhs_type_id)
                ),
                nst.expressions[expr].span.clone(),
                (file!(), line!()),
            );
            return self.find_type_id_by_type(&Type::Invalid);
        }

        rhs_type_id
    }

    fn resolve_indirect_assignment(
        &mut self,
        nst: &Nst,
        lhs_expr_id: &ExprId,
        rhs_expr_id: &ExprId,
    ) -> (TypeId, Option<SymbolId>) {
        let lhs_type_id = self.resolve_expression(nst, *lhs_expr_id).0;
        let rhs_type_id = self.resolve_expression(nst, *rhs_expr_id).0;
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
                nst.expressions[*rhs_expr_id].span.clone(),
                (file!(), line!()),
            );
            return (invalid_type_id, None);
        }

        (lhs_type_id, None)
    }

    fn resolve_if(
        &mut self,
        nst: &Nst,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> TypeId {
        let cond_type = self.resolve_expression(nst, cond).0;
        let boolean_type_id = self.find_type_id_by_type(&Type::Boolean);
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        if cond_type != boolean_type_id && cond_type != invalid_type_id {
            self.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    self.find_type_by_type_id(cond_type)
                ),
                nst.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        let true_branch_type_id = self.resolve_expression(nst, true_branch).0;
        let false_branch_type_id = match false_branch {
            None => self.find_type_id_by_type(&Type::Void),
            Some(e) => self.resolve_expression(nst, e).0,
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
                let false_branch = &nst.expressions[false_branch.expect("false branch exists")];
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
    fn resolve_ident_ref(&mut self, nst: &Nst, ident_ref_id: IdentRefId, kind: RequiredSymbolKind) {
        if self.identifier_ref_bindings.contains_key(&ident_ref_id) {
            return;
        }

        let ident = &nst.identifier_refs[ident_ref_id].ident;

        let ident_id = ident.id;

        if let Some(symbol_id) = self.find_symbol_id_by_ident_and_kind(ident_id, kind) {
            self.identifier_ref_bindings
                .insert(ident_ref_id, vec![symbol_id]);
            return;
        }

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
                    ident.span.clone(),
                    (file!(), line!()),
                );
            }
            RequiredSymbolKind::Other => {
                self.diagnostics.report_err(
                    format!(
                        "Identifier '{}' not found",
                        self.identifiers.get_by_left(&ident_id).unwrap()
                    ),
                    ident.span.clone(),
                    (file!(), line!()),
                );
            }
        }

        // still, resolve it to an unknown symbol
        self.identifier_ref_bindings
            .insert(ident_ref_id, vec![self.not_found_symbol_id]);
    }

    fn resolve_access(
        &mut self,
        nst: &Nst,
        span: &Span,
        expr_id: ExprId,
        ident_ref_id: IdentRefId,
        ident_ref_kind: RequiredSymbolKind,
    ) -> (TypeId, Option<SymbolId>) {
        let (expr_type_id, symbol_id) = self.resolve_expression(nst, expr_id);

        // todo:feature make sure that fq names start form the root namespace (resolve_expression
        //  crawl the scoped up until it finds the symbol, but we don't want to start descending
        //  the scope tree from an "intermediate" (i.e. no root) level

        let ident_ref = &nst.identifier_refs[ident_ref_id];

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
                            RequiredSymbolKind::Other => self.diagnostics.report_err(
                                format!(
                                    "No symbol '{}' found in '{}'",
                                    self.identifiers.get_by_left(&ident_ref.ident.id).unwrap(),
                                    self.identifiers.get_by_left(ns_ident_id).unwrap(),
                                ),
                                ident_ref.ident.span.clone(),
                                (file!(), line!()),
                            ),
                        }

                        self.not_found_symbol_id
                    }
                };

            self.identifier_ref_bindings
                .insert(ident_ref.id, vec![resolved_symbol_id]);
            return (expr_type_id, Some(resolved_symbol_id));
        }

        // otherwise, we use the type_id
        let ty = self.find_type_by_type_id(expr_type_id);
        match ty {
            Type::Struct(stmt_id, _)
                if matches!(ident_ref_kind, RequiredSymbolKind::Other) =>
            {
                let stmt_id = *stmt_id;
                self.resolve_statement(nst, stmt_id);

                match &nst.statements[stmt_id].kind {
                    NstStatementKind::Struct(ident, _, _, fields) => {
                        let struct_symbol_id =
                            self.struct_bindings.get(&stmt_id).expect("was bound").0;

                        if self.native_symbols.contains(&struct_symbol_id) {
                            self.diagnostics.report_err(
                                format!(
                                    "Native struct {} fields cannot be accessed",
                                    self.identifiers.get_by_left(&ident.id).unwrap()
                                ),
                                span.clone(),
                                (file!(), line!()),
                            );
                            (self.find_type_id_by_type(&Type::Invalid), None)
                        } else {
                            match fields
                                .iter()
                                .enumerate()
                                .find(|(_, field)| field.identifier.id == ident_ref.ident.id)
                            {
                                Some((index, _)) => {
                                    let (field_symbol_id, field_type_id) = self
                                        .field_bindings
                                        .get(&(stmt_id, index))
                                        .expect("was bound");

                                    self.identifier_ref_bindings
                                        .insert(ident_ref.id, vec![*field_symbol_id]);

                                    // the field's type was resolved
                                    (*field_type_id, Some(*field_symbol_id))
                                }
                                None => {
                                    self.diagnostics.report_err(
                                        format!(
                                            "No field '{}' found in struct {}",
                                            self.identifiers
                                                .get_by_left(&ident_ref.ident.id)
                                                .unwrap(),
                                            self.identifiers.get_by_left(&ident.id).unwrap()
                                        ),
                                        ident_ref.ident.span.clone(),
                                        (file!(), line!()),
                                    );
                                    self.identifier_ref_bindings
                                        .insert(ident_ref.id, vec![self.not_found_symbol_id]);
                                    (self.find_type_id_by_type(&Type::Invalid), None)
                                }
                            }
                        }
                    }
                    k => panic!("struct expected, got {k:?}"),
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
                        self.identifier_ref_bindings
                            .insert(ident_ref.id, vec![*symbol_id]);
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
                            RequiredSymbolKind::Other => self.diagnostics.report_err(
                                format!("Expected namespace or struct type, got {}", ty),
                                nst.expressions[expr_id].span.clone(),
                                (file!(), line!()),
                            ),
                        }

                        // this it not always true (the left hand side can be a symbol), but it not
                        // being a struct field anyway, considering we did not find any symbol is
                        // (probably) fine...
                        self.identifier_ref_bindings
                            .insert(ident_ref.id, vec![self.not_found_symbol_id]);
                        (self.find_type_id_by_type(&Type::Invalid), None)
                    }
                }
            }
        }
    }

    fn resolve_function_call(&mut self, nst: &Nst, expr_id: ExprId, params: &[ExprId]) -> TypeId {
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        let mut param_types = Vec::with_capacity(params.len());
        for param in params {
            let param_type = self.resolve_expression(nst, *param).0;

            if param_type != invalid_type_id {
                param_types.push(param_type)
            }
        }

        if param_types.len() != params.len() {
            return invalid_type_id;
        }

        if let Some(type_id) = self.expression_types.get(&expr_id) {
            return *type_id;
        }

        let expr = &nst.expressions[expr_id];

        let (fn_type_id, symbol_id) = match &expr.kind {
            ExpressionKind::Literal(Literal {
                kind: LiteralKind::Identifier(ident_ref_id),
                ..
            }) => {
                self.resolve_ident_ref(
                    nst,
                    *ident_ref_id,
                    RequiredSymbolKind::Function(&param_types),
                );
                let symbol_ids = self
                    .identifier_ref_bindings
                    .get(ident_ref_id)
                    .expect("was bound");
                debug_assert!(symbol_ids.len() <= 1);
                let type_id = symbol_ids
                    .first()
                    .map(|s| self.symbols[*s].type_id)
                    .unwrap_or(invalid_type_id);

                (type_id, symbol_ids.first().cloned())
            }
            ExpressionKind::Access(expr_id, ident_ref_id) => self.resolve_access(
                nst,
                &expr.span,
                *expr_id,
                *ident_ref_id,
                RequiredSymbolKind::Function(&param_types),
            ),
            kind => panic!("expected literal or access, got {:?}", kind),
        };

        self.expression_types.insert(expr_id, fn_type_id);

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
        nst: &Nst,
        cond: ExprId,
        expr: ExprId,
    ) -> (TypeId, Option<SymbolId>) {
        let cond_type = self.resolve_expression(nst, cond).0;
        let boolean_type_id = self.find_type_id_by_type(&Type::Boolean);
        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        if cond_type != boolean_type_id && cond_type != invalid_type_id {
            self.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    self.find_type_by_type_id(cond_type)
                ),
                nst.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        self.resolve_expression(nst, expr)
    }

    fn resolve_block(&mut self, nst: &Nst, stmts: &[StmtId]) -> TypeId {
        self.scopes.push();

        self.insert_functions(nst, stmts, false);
        let stmts_type_id = self.resolve_statements(nst, stmts);

        self.scopes.pop();

        stmts_type_id
    }

    fn resolve_struct_instantiation(
        &mut self,
        nst: &Nst,
        ident_ref_id: IdentRefId,
        type_parameters: &[TypeDefId],
        field_expressions: &[(IdentRefId, ExprId)],
        span: &Span,
    ) -> TypeId {
        self.resolve_ident_ref(nst, ident_ref_id, RequiredSymbolKind::Other);
        let stmt_id = match self
            .identifier_ref_bindings
            .get(&ident_ref_id)
            .expect("was bound")
            .iter()
            .filter_map(|sid| match &self.symbols[*sid].kind {
                SymbolKind::Struct(_, stmt_id) => Some(*stmt_id),
                _ => None,
            })
            .enumerate()
            .inspect(|(index, stmt_id)| {
                debug_assert_eq!(
                    *index, 0,
                    "we can have at most one struct, found a 2nd one: {stmt_id}"
                )
            })
            .next()
            .map(|d| d.1)
        {
            None => return self.find_type_id_by_type(&Type::Invalid),
            Some(stmt_id) => stmt_id,
        };

        self.resolve_statement(nst, stmt_id);

        let (struct_identifier, _, type_parameter_identifiers, fields) =
            nst.statements[stmt_id].as_struct();

        if field_expressions.len() != fields.len() {
            self.diagnostics.report_err(
                "Struct fields differ in length",
                span.clone(),
                (file!(), line!()),
            );
        }

        let symbol_id = self
            .struct_bindings
            .get(&stmt_id)
            .expect("struct symbol exists")
            .0;

        if self.native_symbols.contains(&symbol_id) {
            self.diagnostics.report_err(
                format!(
                    "Native struct {} cannot be instantiated",
                    self.identifiers.get_by_left(&struct_identifier.id).unwrap()
                ),
                span.clone(),
                (file!(), line!()),
            );
        }

        let mut local_type_parameters_bindings = type_parameters
            .iter()
            .enumerate()
            .map(|(index, type_def_id)| {
                let field_type_id = self
                    .field_bindings
                    .get(&(stmt_id, index))
                    .expect("was bound")
                    .1;

                let type_def = &nst.type_defs[*type_def_id];
                let type_id = self.resolve_type_def(nst, *type_def_id, false);

                (field_type_id, (type_def.span.clone(), type_id))
            })
            .collect::<HashMap<_, _>>();

        let typed_field_expressions = field_expressions
            .iter()
            .map(|(ident_ref_id, expr_id)| {
                (
                    *ident_ref_id,
                    *expr_id,
                    self.resolve_expression(nst, *expr_id).0,
                )
            })
            .collect::<Vec<_>>();

        for (field_ident_ref_id, field_expr_id, expr_type_id) in typed_field_expressions {
            let field_ident_ref = &nst.identifier_refs[field_ident_ref_id];

            if let Some((index, field)) = fields
                .iter()
                .enumerate()
                .find(|(_, field)| field.identifier.id == field_ident_ref.ident.id)
            {
                let field_symbol_id = self
                    .field_bindings
                    .get(&(stmt_id, index))
                    .expect("field bound")
                    .0;

                self.identifier_ref_bindings
                    .insert(field_ident_ref_id, vec![field_symbol_id]);

                let field_type_id = self
                    .field_bindings
                    .get(&(stmt_id, index))
                    .expect("was bound")
                    .1;

                let ty = self.types.get_by_left(&field_type_id).expect("type exists");
                if let Type::Parameter(_, index) = ty {
                    let span = nst.expressions[field_expr_id].span.clone();
                    if let Some(previous_binding) =
                        local_type_parameters_bindings.insert(field_type_id, (span, expr_type_id))
                    {
                        if previous_binding.1 != expr_type_id {
                            let index = &type_parameter_identifiers[*index];
                            let type_parameter_ident = self
                                .identifiers
                                .get_by_left(&index.id)
                                .expect("identifier exists");
                            self.diagnostics.report_err(
                                format!(
                                    "Invalid type for field '{}': expected {}, got {} ({} bound at line {}, column {})",
                                    self.identifiers.get_by_left(&field.identifier.id).unwrap(),
                                    self.find_type_by_type_id(previous_binding.1),
                                    self.find_type_by_type_id(expr_type_id),
                                    type_parameter_ident,
                                    previous_binding.0.line,
                                    previous_binding.0.column
                                ),
                                nst.expressions[field_expr_id].span.clone(),
                                (file!(), line!()),
                            );
                        }
                    }
                } else if expr_type_id != field_type_id {
                    self.diagnostics.report_err(
                        format!(
                            "Invalid type for field '{}': expected {}, got {}",
                            self.identifiers.get_by_left(&field.identifier.id).unwrap(),
                            self.find_type_by_type_id(field_type_id),
                            self.find_type_by_type_id(expr_type_id)
                        ),
                        nst.expressions[field_expr_id].span.clone(),
                        (file!(), line!()),
                    )
                }
            } else {
                // the field was not found by its name...
                self.identifier_ref_bindings
                    .insert(field_ident_ref_id, vec![self.not_found_symbol_id]);
            }
        }

        if !local_type_parameters_bindings.is_empty() {
            let mut resolved_type_parameters = local_type_parameters_bindings
                .into_iter()
                .map(|(type_param_type_id, (_, type_id))| {
                    (
                        self.find_type_by_type_id(type_param_type_id)
                            .as_parameter()
                            .1,
                        type_id,
                    )
                })
                .collect::<Vec<_>>();

            resolved_type_parameters
                .iter()
                .for_each(|(index, type_id)| {
                    self.type_parameters.insert((stmt_id, *index), *type_id);
                });

            // todo add to self.something
            resolved_type_parameters.sort_by(|a, b| a.0.cmp(&b.0));
            let types = resolved_type_parameters
                .into_iter()
                .map(|v| v.1)
                .collect::<Vec<_>>();

            self.insert_type(Type::Struct(stmt_id, types))
        } else {
            self.find_type_id_by_identifier(struct_identifier.id)
                .expect("type exists")
        }
    }

    fn resolve_array_instantiation(&mut self, nst: &Nst, values: &[ExprId]) -> TypeId {
        let expected_type_id = self
            .resolve_expression(
                nst,
                *values.first().expect("array has at least one element"),
            )
            .0;

        if matches!(
            self.types.get_by_left(&expected_type_id).unwrap(),
            Type::Void
        ) {
            self.diagnostics.report_err(
                "Void values cannot be used as array elements at index 0".to_string(),
                nst.expressions[*values.first().unwrap()].span.clone(),
                (file!(), line!()),
            );
            return self.find_type_id_by_type(&Type::Invalid);
        }

        for (index, expr_id) in values.iter().enumerate().skip(1) {
            let type_id = self.resolve_expression(nst, *expr_id).0;
            if type_id != expected_type_id {
                self.diagnostics.report_err(
                    format!(
                        "Expected value of type {expected_type}, got {actual_type} at index {index}",
                        expected_type = self.find_type_by_type_id(expected_type_id),
                        actual_type = self.find_type_by_type_id(type_id)
                    ),
                    nst.expressions[*expr_id].span.clone(),
                    (file!(), line!()),
                );
            }
        }

        self.insert_type(Type::Array(expected_type_id, values.len()))
    }

    fn resolve_array_access(
        &mut self,
        nst: &Nst,
        base_expr_id: ExprId,
        value_expr_id: ExprId,
    ) -> TypeId {
        let array_type_id = self.resolve_expression(nst, base_expr_id).0;
        let array_type = self.find_type_by_type_id(array_type_id);

        let type_id = match array_type {
            Type::Array(elements_type_id, _) => *elements_type_id,
            _ => {
                self.diagnostics.report_err(
                    format!("Expected type array, got {}", array_type),
                    nst.expressions[base_expr_id].span.clone(),
                    (file!(), line!()),
                );
                self.find_type_id_by_type(&Type::Invalid)
            }
        };

        let index_type_id = self.resolve_expression(nst, value_expr_id).0;
        if !matches!(self.find_type_by_type_id(index_type_id), Type::Number) {
            self.diagnostics.report_err(
                format!(
                    "Expected index to be of type number, got {}",
                    self.find_type_by_type_id(index_type_id)
                ),
                nst.expressions[base_expr_id].span.clone(),
                (file!(), line!()),
            );
        }

        type_id
    }

    fn resolve_statements(&mut self, nst: &Nst, stmts: &[StmtId]) -> TypeId {
        let mut ret_type = self.find_type_id_by_type(&Type::Void);

        for &stmt_id in stmts {
            let stmt = &nst.statements[stmt_id];
            if matches!(stmt.kind, NstStatementKind::Namespace(..)) {
                self.diagnostics.report_err(
                    "Namespace invalid at this location",
                    stmt.span.clone(),
                    (file!(), line!()),
                );
                return self.find_type_id_by_type(&Type::Invalid);
            }
            self.resolve_statement(nst, stmt_id);

            let stmt_type = match &stmt.kind {
                NstStatementKind::Expression(e) => {
                    *self.expression_types.get(e).expect("was typed")
                }
                NstStatementKind::Let(..) => self.find_type_id_by_type(&Type::Void),
                NstStatementKind::Ret(..) => self.find_type_id_by_type(&Type::None),
                NstStatementKind::LetFn(..) => self.find_type_id_by_type(&Type::Void),
                NstStatementKind::Struct(..) => self.find_type_id_by_type(&Type::Void),
                NstStatementKind::Annotation(..) => self.find_type_id_by_type(&Type::Void),
                NstStatementKind::Use(..) => self.find_type_id_by_type(&Type::Void),
                NstStatementKind::Namespace(..) => self.find_type_id_by_type(&Type::Invalid),
            };

            if ret_type != self.find_type_id_by_type(&Type::None) {
                ret_type = stmt_type
            }
        }

        ret_type
    }

    fn resolve_statement(&mut self, nst: &Nst, stmt_id: StmtId) -> TypeId {
        // todo skip if already resolved?
        let stmt = &nst.statements[stmt_id];
        match &stmt.kind {
            NstStatementKind::Expression(expr_id) => self.resolve_expression(nst, *expr_id).0,
            NstStatementKind::Let(ident, expr_id) => {
                self.resolve_let(nst, stmt_id, ident, *expr_id);

                self.find_type_id_by_type(&Type::Void)
            }
            NstStatementKind::Ret(expr, _) => {
                if let Some(expr_id) = expr {
                    self.resolve_expression(nst, *expr_id);
                }

                self.find_type_id_by_type(&Type::None)
            }
            NstStatementKind::LetFn(..) => {
                self.resolve_function(nst, stmt_id);
                self.find_type_id_by_type(&Type::Void)
            }
            NstStatementKind::Struct(..) => {
                self.resolve_struct(nst, stmt_id);
                self.find_type_id_by_type(&Type::Void)
            }
            NstStatementKind::Annotation(..) => self.find_type_id_by_type(&Type::Void),
            NstStatementKind::Use(..) => {
                self.resolve_use(nst, stmt_id);
                self.find_type_id_by_type(&Type::Void)
            }
            NstStatementKind::Namespace(..) => {
                self.resolve_namespace(nst, stmt_id);
                self.scopes.pop();
                self.find_type_id_by_type(&Type::Void)
            }
        }
    }

    fn resolve_let(
        &mut self,
        nst: &Nst,
        stmt_id: StmtId,
        ident: &transmute_nst::nodes::Identifier,
        expr: ExprId,
    ) {
        if self.let_bindings.contains_key(&stmt_id) {
            return;
        }

        let expr_type_id = self.resolve_expression(nst, expr).0;

        if expr_type_id == self.find_type_id_by_type(&Type::None) {
            self.diagnostics.report_err(
                format!("Expected some type, got {}", Type::None),
                nst.expressions[expr].span.clone(),
                (file!(), line!()),
            );
        }
        if expr_type_id == self.find_type_id_by_type(&Type::Void) {
            self.diagnostics.report_err(
                format!("Expected some type, got {}", Type::Void),
                nst.expressions[expr].span.clone(),
                (file!(), line!()),
            );
        }

        let symbol_id =
            self.insert_symbol(ident.id, SymbolKind::Let(ident.id, stmt_id), expr_type_id);

        self.let_bindings.insert(stmt_id, symbol_id);
    }

    /// Resolves a function, starting by inserting all structs contained in the function (but not
    /// in nested functions). See `insert_structs`.
    fn resolve_function(&mut self, nst: &Nst, stmt_id: StmtId) {
        if let Some(parent) = self.fn_stack.last().cloned() {
            self.parent.insert(stmt_id, parent);
        }

        let (ident, annotations, params, body_expr_id) = nst.statements[stmt_id].as_function();
        self.fn_stack.push(stmt_id);
        self.scopes.push();

        if let ExpressionKind::Block(stmt_ids) = &nst.expressions[*body_expr_id].kind {
            let stmt_ids = stmt_ids
                .iter()
                .filter(|stmt_id| {
                    matches!(nst.statements[**stmt_id].kind, NstStatementKind::Struct(..))
                })
                .copied()
                .collect::<Vec<StmtId>>();
            self.insert_structs(nst, &stmt_ids);
        }

        let invalid_type_id = self.find_type_id_by_type(&Type::Invalid);

        let (fn_symbol_id, param_types, ret_type_id) = self
            .fn_bindings
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

        for (index, (parameter, type_id)) in params.iter().zip(param_types).enumerate() {
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
            } else {
                let symbol_id = self.insert_symbol(ident_id, symbol_kind, type_id);

                self.parameter_bindings
                    .insert((stmt_id, index), (symbol_id, type_id));
            }
        }

        for annotation in annotations.iter() {
            self.resolve_ident_refs(nst, &annotation.ident_ref_ids, false);
        }

        let is_native = self.is_native_annotation_present(nst, annotations);
        if is_native {
            self.native_symbols.insert(fn_symbol_id);

            let expression = &nst.expressions[*body_expr_id];
            let has_body = match &expression.kind {
                ExpressionKind::Block(stmt_ids) => {
                    // because the implicit ret runs before the resolution, empty function
                    // bodies actually have exactly one implicit ret none.
                    !(stmt_ids.len() == 1
                        && matches!(
                            &nst.statements[stmt_ids[0]].kind,
                            &NstStatementKind::Ret(None, RetMode::Implicit)
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
        //todo:refactor review since we cannot have "holes" anymore...
        self.resolve_expression(nst, *body_expr_id);

        if !is_native && ret_type_id != invalid_type_id {
            let exit_points = nst
                .exit_points
                .exit_points
                .get(body_expr_id)
                .expect("exit points is computed")
                .iter()
                .map(|e| match e {
                    ExitPoint::Explicit(e) => (*e, true),
                    ExitPoint::Implicit(e) => (*e, false),
                })
                .collect::<Vec<_>>();

            assert!(
                !exit_points.is_empty(),
                "we must always have at least one exit point, even if implicit and void"
            );

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
                    Some(exit_expr_id) => self.resolve_expression(nst, exit_expr_id).0,
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
                        nst.expressions[exit_expr_id].span.clone()
                    } else {
                        nst.expressions[*body_expr_id].span.clone()
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

        self.fn_stack.pop();
        self.scopes.pop();
    }

    fn resolve_struct(&mut self, nst: &Nst, stmt_id: StmtId) {
        if self
            .struct_bindings
            .get(&stmt_id)
            .map(|b| b.1)
            .unwrap_or(false)
        {
            return;
        }

        if let Some(parent) = self.fn_stack.last().cloned() {
            self.parent.insert(stmt_id, parent);
        }

        let (identifier, annotations, type_parameters, fields) =
            nst.statements[stmt_id].as_struct();

        for (index, type_parameter) in type_parameters.iter().enumerate() {
            self.insert_symbol(
                type_parameter.id,
                SymbolKind::TypeParameter(identifier.id, stmt_id, index),
                self.find_type_id_by_type(&Type::Type),
            );
            self.insert_type(Type::Parameter(stmt_id, index));
        }

        for annotation in annotations {
            self.resolve_ident_refs(nst, &annotation.ident_ref_ids, false);
        }

        let is_native = self.is_native_annotation_present(nst, annotations);
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

        // struct fields are in the scope of the struct itself, we want to make sure that no other
        // field with the same name exists in the current struct, but the same identifier might
        // exist outside and this is not an issue
        self.scopes.push();

        for (index, field) in fields.iter().enumerate() {
            let type_id = self.resolve_type_def(nst, field.type_def_id, false);

            let ident_id = field.identifier.id;
            let symbol_kind = SymbolKind::Field(ident_id, stmt_id, index);

            let symbol_id = if self.is_symbol_in_current_scope(ident_id, &symbol_kind) {
                self.diagnostics.report_err(
                    format!(
                        "Field '{ident}' is already defined",
                        ident = self.identifiers.get_by_left(&ident_id).unwrap(),
                    ),
                    field.identifier.span.clone(),
                    (file!(), line!()),
                );
                self.not_found_symbol_id
            } else {
                self.insert_symbol(ident_id, symbol_kind, type_id)
            };
            self.field_bindings
                .insert((stmt_id, index), (symbol_id, type_id));
        }

        let symbol_id = self
            .struct_bindings
            .get(&stmt_id)
            .map(|b| b.0)
            // it may happen that the struct is not found in case of duplicate def.
            .unwrap_or(self.not_found_symbol_id);

        if is_native {
            self.native_symbols.insert(symbol_id);
        }

        self.struct_bindings
            .entry(stmt_id)
            .and_modify(|(_, resolved)| *resolved = true)
            .or_insert((symbol_id, true));

        self.scopes.pop();
    }

    fn resolve_use(&mut self, nst: &Nst, stmt_id: StmtId) {
        let ident_ref_ids = nst.statements[stmt_id].as_use();
        self.resolve_ident_refs(nst, ident_ref_ids, false);

        let ident_id = nst.identifier_refs[*ident_ref_ids.last().unwrap()].ident.id;

        self.identifier_ref_bindings
            .get(ident_ref_ids.last().unwrap())
            .expect("was bound")
            .iter()
            .for_each(|id| self.scopes.push_symbol(ident_id, *id));
    }

    fn resolve_namespace(&mut self, nst: &Nst, stmt_id: StmtId) {
        let (_, _, stmt_ids) = nst.statements[stmt_id].as_namespace();
        self.scopes.push();

        self.bring_namespace_symbols_into_scope(*self.namespace_bindings.get(&stmt_id).unwrap());

        for stmt_id in stmt_ids.iter() {
            self.resolve_statement(nst, *stmt_id);
        }
    }

    /// Resolve `ident_refs` involved in fully qualified names. Intermediate identifier refs are
    /// pointing to namespaces, final one to any kind of symbol. If `ignore_not_found` is `true`,
    /// no errors will be reported and the failed resolution will be put back in the
    /// `Nst` so that a next phase can resolve them.
    fn resolve_ident_refs(
        &mut self,
        nst: &Nst,
        ident_ref_ids: &[IdentRefId],
        ignore_not_found: bool,
    ) {
        if ident_ref_ids.len() == 1 {
            self.resolve_ident_ref(nst, ident_ref_ids[0], RequiredSymbolKind::Other);
            return;
        }

        let mut parent_found = true;
        let mut namespace_id = *self.namespace_stack.root().unwrap();

        for ident_ref_id in ident_ref_ids[0..ident_ref_ids.len() - 1].iter() {
            if self.identifier_ref_bindings.contains_key(ident_ref_id) {
                continue;
            }

            let ident_ref = &nst.identifier_refs[*ident_ref_id];

            if !parent_found {
                self.identifier_ref_bindings
                    .insert(*ident_ref_id, vec![self.not_found_symbol_id]);
                continue;
            }

            if let SymbolKind::Namespace(_, symbols) = &self.symbols[namespace_id].kind {
                if let Some(symbol_id) =
                    symbols.find(&self.symbols, ident_ref.ident.id, RequiredSymbolKind::Other)
                {
                    self.identifier_ref_bindings
                        .insert(*ident_ref_id, vec![symbol_id]);
                    namespace_id = symbol_id;
                    continue;
                }
            }

            if ignore_not_found {
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

            self.identifier_ref_bindings
                .insert(*ident_ref_id, vec![self.not_found_symbol_id]);
            parent_found = false;
        }

        let ident_ref_id = ident_ref_ids[ident_ref_ids.len() - 1];

        if self.identifier_ref_bindings.contains_key(&ident_ref_id) {
            return;
        }

        let ident_ref = &nst.identifier_refs[ident_ref_id];

        if !parent_found {
            if !ignore_not_found {
                self.identifier_ref_bindings
                    .insert(ident_ref_id, vec![self.not_found_symbol_id]);
            }
            return;
        }

        if !matches!(self.symbols[namespace_id].kind, SymbolKind::Namespace(..)) {
            if !ignore_not_found {
                let parent_ident_ref_id = ident_ref_ids[ident_ref_ids.len() - 2];
                let parent_ident_id = nst
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
                    nst.identifier_refs[parent_ident_ref_id].ident.span.clone(),
                    (file!(), line!()),
                );
            }
            self.identifier_ref_bindings
                .insert(ident_ref_id, vec![self.not_found_symbol_id]);
            return;
        }

        let symbol_ids = self.symbols[namespace_id]
            .as_namespace()
            .get(&ident_ref.ident.id)
            .cloned()
            .unwrap_or_default();

        if !symbol_ids.is_empty() {
            self.identifier_ref_bindings
                .insert(ident_ref_id, symbol_ids);
        } else if !ignore_not_found {
            self.diagnostics.report_err(
                format!(
                    "Symbol '{}' not found",
                    self.identifiers.get_by_left(&ident_ref.ident.id).unwrap()
                ),
                ident_ref.ident.span.clone(),
                (file!(), line!()),
            );
            self.identifier_ref_bindings
                .insert(ident_ref_id, vec![self.not_found_symbol_id]);
        }
    }

    /// Resolves a `TypeDefId`. Starts by resolving all potential `IdentRefId`s found and resolves
    /// the `TypeDefId` to that last found type. By default, issues a diagnostic when the type
    /// found is not assignable (as per `Type::is_assignable()` definition). If `return_type` is
    /// set to `true` however, the type validity is checked with `Type::is_valid_return_type()`.
    fn resolve_type_def(&mut self, nst: &Nst, type_def_id: TypeDefId, return_type: bool) -> TypeId {
        match &nst.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                let ident_ref_ids = ident_ref_ids.clone();
                self.resolve_ident_refs(nst, &ident_ref_ids, false);

                let ident_ref_id = *ident_ref_ids.last().unwrap();
                let symbol_ids = self
                    .identifier_ref_bindings
                    .get(&ident_ref_id)
                    .expect("was bound");

                debug_assert_eq!(symbol_ids.len(), 1);
                let symbol_id = symbol_ids[0];

                // todo:refactoring why not use the TypeId from the symbol, and lookup the Type from
                //  there?
                let ty = match &self.symbols[symbol_id].kind {
                    SymbolKind::Struct(_, stmt_id) => {
                        // todo:feature add support for type parameters to TypeDef
                        Type::Struct(*stmt_id, vec![])
                    }
                    SymbolKind::NativeType(_, ty) => ty.clone(),
                    SymbolKind::TypeParameter(_, stmt_id, index) => {
                        Type::Parameter(*stmt_id, *index)
                    }
                    SymbolKind::NotFound => {
                        // nothing, we reported already
                        return self.find_type_id_by_type(&Type::Invalid);
                    }
                    _ => {
                        let ident = &nst.identifier_refs[ident_ref_id].ident;
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
                        nst.type_defs[type_def_id].span.clone(),
                        (file!(), line!()),
                    )
                }
            }
            TypeDefKind::Array(type_def_id, _) => {
                self.resolve_type_def(nst, *type_def_id, false);
            }
        }

        self.find_type_id_by_type_def_id(nst, type_def_id)
            .unwrap_or_else(|| self.find_type_id_by_type(&Type::Invalid))
    }

    fn is_native_annotation_present(&self, nst: &Nst, annotations: &[Annotation]) -> bool {
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
                            .get_by_left(&nst.identifier_refs.get(id).unwrap().ident.id)
                            .unwrap(),
                    )
                })
                .take_while(|(left, right)| left == right)
                .count();

            if match_len != NATIVE_ANNOTATION.len() {
                continue;
            }

            let symbol_ids = self
                .identifier_ref_bindings
                .get(annotation.ident_ref_ids.last().unwrap())
                .expect("was bound");

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
    fn insert_namespace(&mut self, nst: &Nst, stmt_id: StmtId) -> SymbolId {
        let statement = &nst.statements[stmt_id];
        let (namespace_ident, _, namespace_stmts) = statement.as_namespace();

        if let Some(namespace_symbol_id) = self.namespace_stack.last() {
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
        self.namespace_bindings.insert(stmt_id, symbol_id);

        self.bring_symbol_into_namespace(namespace_ident.id, symbol_id);

        self.namespace_stack.push(symbol_id);
        self.scopes.push();

        self.insert_namespaces(nst, namespace_stmts);
        self.insert_annotations(nst, namespace_stmts);
        self.insert_structs(nst, namespace_stmts);

        self.scopes.pop();
        self.namespace_stack.pop();

        symbol_id
    }

    fn insert_namespaces(&mut self, nst: &Nst, stmts: &[StmtId]) {
        let namespaces = stmts
            .iter()
            .filter_map(|stmt| nst.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                NstStatementKind::Namespace(..) => Some(stmt.id),
                _ => None,
            })
            .collect::<Vec<_>>();

        namespaces.into_iter().for_each(|stmt| {
            self.insert_namespace(nst, stmt);
        });
    }

    fn insert_namespace_functions(&mut self, hir: &Nst, stmt_id: StmtId) {
        let namespace_symbol_id = *self.namespace_bindings.get(&stmt_id).unwrap();

        self.namespace_stack.push(namespace_symbol_id);
        self.scopes.push();

        self.bring_namespace_symbols_into_scope(namespace_symbol_id);

        let (_, _, stmts) = hir.statements[stmt_id].as_namespace();
        self.insert_namespaces_functions(hir, stmts);
        self.insert_functions(hir, stmts, true);

        self.scopes.pop();
        self.namespace_stack.pop();
    }

    /// Inserts all top level functions contained in namespaces which `StmtId` are provided.
    fn insert_namespaces_functions(&mut self, nst: &Nst, stmts: &[StmtId]) {
        let namespaces = stmts
            .iter()
            .filter_map(|stmt| nst.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                NstStatementKind::Namespace(..) => Some(stmt.id),
                _ => None,
            })
            .collect::<Vec<_>>();

        namespaces
            .into_iter()
            .for_each(|stmt| self.insert_namespace_functions(nst, stmt));
    }

    /// Inserts all functions found in `stmts` into `self.function_bindings` (which itself contains
    /// reference to `self.symbols`) as well as the current scope's symbol table, and if
    /// `top_level` is `true` into the current namespace.
    fn insert_functions(&mut self, nst: &Nst, stmts: &[StmtId], top_level: bool) {
        for stmt_id in stmts.iter() {
            let stmt = &nst.statements[*stmt_id];

            match &stmt.kind {
                NstStatementKind::LetFn(ident, _, params, ret, ..) => {
                    let parameter_types = params
                        .iter()
                        .map(|p| p.type_def_id)
                        .map(|type_def_id| self.resolve_type_def(nst, type_def_id, false))
                        .collect::<Vec<_>>();

                    let ret_type = ret
                        .type_def_id
                        .map(|type_def_id| self.resolve_type_def(nst, type_def_id, true))
                        .unwrap_or(self.find_type_id_by_type(&Type::Void));
                    self.fn_return_types.insert(*stmt_id, ret_type);

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
                        self.let_bindings.insert(*stmt_id, symbol_id);
                        self.fn_bindings.insert(*stmt_id, symbol_id);

                        if top_level {
                            self.bring_symbol_into_namespace(ident.id, symbol_id);
                        }

                        if let Some(target_type_id) = target_type_id {
                            self.type_functions
                                .entry(target_type_id)
                                .or_default()
                                .insert(ident.id, symbol_id);
                        }
                    }
                }
                NstStatementKind::Use(path) => {
                    self.resolve_ident_refs(nst, path, true);
                    if let Some(symbol_ids) = self.identifier_ref_bindings.get(path.last().unwrap())
                    {
                        let ident_id = nst.identifier_refs[*path.last().unwrap()].ident.id;
                        symbol_ids
                            .iter()
                            .for_each(|id| self.scopes.push_symbol(ident_id, *id));
                    }
                }
                _ => (),
            }
        }
    }

    /// Inserts all structs found in `stmts` into `self.struct_bindings` (which itself contains
    /// reference to `self.symbols`) as well as the current stack frame's symbol table, and if
    /// `self.fn_stack.last()` is `None` into the current namespace. While doing so, we perform
    /// the following:
    ///  - insert a type corresponding to the struct in `self.types`;
    ///  - verify that no struct with the same name already exist in the current scope;
    ///  - resolve the fields' types.
    fn insert_structs(&mut self, hir: &Nst, stmts: &[StmtId]) {
        for (stmt_id, identifier) in stmts
            .iter()
            .map(|stmt| {
                hir.statements
                    .get(*stmt)
                    .unwrap_or_else(|| panic!("{stmt:?} exists"))
            })
            .filter_map(|stmt| match &stmt.kind {
                NstStatementKind::Struct(ident, ..) => Some((stmt.id, ident)),
                _ => None,
            })
        {
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
                let struct_type_id = self.insert_type(Type::Struct(stmt_id, vec![]));
                let symbol_id = self.insert_symbol(ident_id, symbol_kind, struct_type_id);

                if self.fn_stack.last().is_none() {
                    self.bring_symbol_into_namespace(ident_id, symbol_id);
                }

                self.struct_bindings.insert(stmt_id, (symbol_id, false));
            }
        }
    }

    /// Inserts all annotations found in `stmts` into `self.annotations_symbols` (which itself
    /// contains reference to `self.symbols`) as well as the current stack frame's symbol table,
    /// and into the current namespace.
    fn insert_annotations(&mut self, hir: &Nst, stmts: &[StmtId]) {
        let annotations = stmts
            .iter()
            .filter_map(|stmt| hir.statements.get(*stmt))
            .filter_map(|stmt| match &stmt.kind {
                NstStatementKind::Annotation(ident) => Some((stmt.id, ident.clone())),
                _ => None,
            })
            .collect::<Vec<_>>();

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

                self.annotation_bindings.insert(stmt_id, symbol_id);
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
    fn find_type_id_by_type_def_id(&mut self, nst: &Nst, type_def_id: TypeDefId) -> Option<TypeId> {
        match &nst.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                if ident_ref_ids.clone().len() == 1 {
                    // todo merge with the more general case in order to lift the documented
                    //  assumption
                    let ident_id = nst.identifier_refs[ident_ref_ids.clone()[0]].ident.id;
                    self.find_type_id_by_identifier(ident_id)
                } else {
                    let symbol_id = self.find_symbol_by_ident_ref_ids(nst, ident_ref_ids)?;

                    match &self.symbols[symbol_id].kind {
                        SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                        SymbolKind::Struct(_, stmt) => Some(
                            // todo:feature add support for type parameters to TypeDef
                            self.find_type_id_by_type(&Type::Struct(*stmt, vec![])),
                        ),
                        _ => None,
                    }
                }
            }
            TypeDefKind::Array(type_def_id, len) => self
                .find_type_id_by_type_def_id(nst, *type_def_id)
                .map(|base| Type::Array(base, *len))
                .map(|t| self.insert_type(t)),
        }
    }

    fn find_type_id_by_identifier(&self, ident_id: IdentId) -> Option<TypeId> {
        self.find_symbol_id_by_ident_and_kind(ident_id, RequiredSymbolKind::Other)
            // todo:refactoring why not use the TypeId from the symbol directly?
            .and_then(|symbol_id| match &self.symbols[symbol_id].kind {
                SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                SymbolKind::TypeParameter(_, stmt_id, index) => {
                    Some(self.find_type_id_by_type(&Type::Parameter(*stmt_id, *index)))
                }
                SymbolKind::Struct(_, stmt) => {
                    // there are no type parameters on an identifier, we can use an empty types
                    // list
                    Some(self.find_type_id_by_type(&Type::Struct(*stmt, vec![])))
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
                resolver.symbols[*resolver.namespace_stack.root().unwrap()].as_namespace();
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

    /// Resolved a `Type::Parameter(..)` type to the actual `TypeId`
    fn find_type_parameter_actual_type_id(&self, type_id: TypeId) -> TypeId {
        let expr_type = self.find_type_by_type_id(type_id);
        match expr_type {
            Type::Parameter(stmt_id, index) => *self
                .type_parameters
                .get(&(*stmt_id, *index))
                .expect("type exists"),
            _ => type_id,
        }
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

    /// Finds the `SymbolId` that the `ident_ids` refer to. Does not try to resolve `IdentifierRef`
    /// on the way.
    fn find_symbol_by_ident_ref_ids(
        &mut self,
        nst: &Nst,
        ident_ref_ids: &[IdentRefId],
    ) -> Option<SymbolId> {
        debug_assert!(!ident_ref_ids.is_empty());

        if ident_ref_ids.len() == 1 {
            todo!("Search for symbol in current scope, crawling up as needed")
        }

        fn extract_ident_and_span(nst: &Nst, ident_ref_id: IdentRefId) -> (IdentId, &Span) {
            nst.identifier_refs
                        .get(ident_ref_id)
                        .map(|ident_ref| (ident_ref.ident.id, &ident_ref.ident.span))
                .unwrap_or_else(|| {
                    panic!(
                        "{:?} neither found in self.identifier_refs={:?} nor in hir.identifier_refs={:?}",
                        ident_ref_id, nst.identifier_refs, nst.identifier_refs
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

        let mut ns_symbols = self.symbols[*self.namespace_stack.root().unwrap()].as_namespace();
        for ident_ref_id in &ident_ref_ids[0..ident_ref_ids.len() - 1] {
            let (ident_id, span) = extract_ident_and_span(nst, *ident_ref_id);
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

        let (ident_id, span) = extract_ident_and_span(nst, *ident_ref_ids.last().unwrap());
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
        if let Some(namespace_symbol_id) = self.namespace_stack.last() {
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
    use crate::natives::Natives;
    use crate::nodes::Expression;
    use crate::nodes::{Implementation, Statement, StatementKind};
    use crate::symbol::Symbol;
    use crate::Hir;
    use insta::assert_debug_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;
    use transmute_nst::nodes::Nst;

    impl Hir {
        fn symbols_with_invalid_type(&self) -> Vec<&Symbol> {
            self.symbols
                .iter()
                .filter(|(id, _)| *id != crate::SymbolId::from(0))
                .map(|(_, symbol)| symbol)
                .filter(|symbol| symbol.type_id == crate::TypeId::from(0))
                .collect()
        }

        fn statements_with_invalid_type(&self) -> Vec<&Statement> {
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
                    StatementKind::Struct(_, _, Implementation::Provided(fields), _) => {
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

        fn expressions_with_invalid_type(&self) -> Vec<&Expression> {
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
                let resolved_hir = crate::Resolver::new().resolve($natives, nst);

                if let Ok(hir) = &resolved_hir {
                    // todo:refactoring move to production code?
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
    test_resolution!(struct_type_parameter, "struct S<T> { f: T }");
    test_resolution!(
        struct_type_parameter_several_use,
        "struct S<T> { f: T, g: T }"
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
        struct_instantiation_out_of_order,
        r#"
        struct S { f1: number, f2: boolean, };
        let s1 = S { f1: 1, f2: true, };
        let s2 = S { f2: false, f1: 2, };
        "#
    );
    test_resolution!(
        struct_instantiation_out_of_order_invlaid_types,
        r#"
        struct S { f1: number, f2: boolean, };
        let s1 = S { f1: 1, f2: true, };
        let s2 = S { f2: 2, f1: false, };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters,
        r#"
        struct S<T> { f: T, };
        let s = S { f: 1, };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters_explicit,
        r#"
        struct S<T> { f: T, };
        let s = S!<number> { f: 1, };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters_explicit_invalid_type,
        r#"
        struct S<T> { f: T, };
        let s = S!<number> { f: true, };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters_incompatible,
        r#"
        struct S<T> { f1: T, f2: T};
        let s = S { f1: 1, f2: true };
        "#
    );
    test_resolution!(
        struct_field_with_type_parameters_as_return_value,
        r#"
        struct S<T> { f: T };
        let f(): number {
            let s = S { f: 1 };
            ret s.f;
        }
        "#
    );
    test_resolution!(
        struct_field_with_type_parameters,
        r#"
        struct S<T> { f: T };
        let s = S { f: 1 };
        let n = 1;
        n = s.f;
        s.f = 2;
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters_reassign,
        r#"
        struct S<T> { f: T };
        let s = S { f: 1 };
        s = S { f: 2 };
        "#
    );
    test_resolution!(
        struct_instantiation_with_type_parameters_reassign_invalid_type,
        r#"
        struct S<T> { f: T };
        let s = S { f: 1 };
        s = S { f: true };
        "#
    );
    // fixme (parsing missing)
    // test_resolution!(
    //     struct_instantiation_with_type_parameters_nested,
    //     r#"
    //     struct Outer<T> { f: Inner!<T>, };
    //     struct Inner<T> { f: T, };
    //     let o = Outer { f: Inner!<number> { field: 1}, };
    //     "#
    // );
    // fixme
    // test_resolution!(
    //     struct_instantiation_out_of_order_fixme,
    //     r#"
    //     struct S1 { field: number };
    //     struct S2 { field: number };
    //     struct S3 {
    //       f1: S1,
    //       f2: S2,
    //     };
    //     let s1 = S3 {
    //       f1: S1 { field: 1 }, f2: S2 { field: 2 }
    //     }; };
    //     let s2 = S3 {
    //       f2: S2 { field: 2 },
    //       f1: S1 { field: 1 }
    //     }; };
    //     "#
    // );

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
