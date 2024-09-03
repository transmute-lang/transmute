use crate::bound::{Bound, Unbound};
use crate::expression::{Expression, ExpressionKind, Target};
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::literal::LiteralKind;
use crate::natives::{Native, Natives, Type};
use crate::passes::exit_points_resolver::ExitPoint;
use crate::statement::{Field, Parameter, Return, Statement, StatementKind};
use crate::symbol::{Symbol, SymbolKind};
use crate::typed::{Typed, Untyped};
use bimap::BiHashMap;
use std::collections::HashMap;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;

pub struct Resolver<'a> {
    exit_points: &'a HashMap<ExprId, Vec<ExitPoint>>,
    unreachable: &'a Vec<ExprId>,
}

// todo add support for struct nested in function (examples/.inner_struct.tm)

type Function<T, B> = (Identifier<B>, Vec<Parameter<T, B>>, Return<T>);

impl<'a> Resolver<'a> {
    pub fn new(
        exit_points: &'a HashMap<ExprId, Vec<ExitPoint>>,
        unreachable: &'a Vec<ExprId>,
    ) -> Self {
        Self {
            exit_points,
            unreachable,
        }
    }

    pub fn resolve(
        &self,
        identifiers: VecMap<IdentId, String>,
        identifier_refs: VecMap<IdentRefId, IdentifierRef<Unbound>>,
        expressions: VecMap<ExprId, Expression<Untyped>>,
        statements: VecMap<StmtId, Statement<Untyped, Unbound>>,
        root: Vec<StmtId>,
        natives: Natives,
    ) -> Result<Output, Diagnostics> {
        let mut types = BiHashMap::default();

        let invalid_type_id = TypeId::from(types.len());
        types.insert(Type::Invalid, invalid_type_id);

        let void_type_id = TypeId::from(types.len());
        types.insert(Type::Void, void_type_id);

        let none_type_id = TypeId::from(types.len());
        types.insert(Type::None, none_type_id);

        let boolean_type_id = TypeId::from(types.len());
        types.insert(Type::Boolean, boolean_type_id);

        let number_type_id = TypeId::from(types.len());
        types.insert(Type::Number, number_type_id);

        let mut symbols = VecMap::<SymbolId, Symbol>::default();
        let not_found_symbol_id = SymbolId::from(symbols.len());
        symbols.push(Symbol {
            id: not_found_symbol_id,
            kind: SymbolKind::NotFound,
            type_id: invalid_type_id,
        });

        // just append all native names, if they are missing
        let mut identifiers = identifiers.into_reversed::<HashMap<_, _>>();
        for native_name in natives.names().into_iter() {
            if !identifiers.contains_key(&native_name) {
                identifiers.insert(native_name, IdentId::from(identifiers.len()));
            }
        }

        let ident_ref_count = identifier_refs.len();
        let expr_count = expressions.len();
        let stmt_count = statements.len();

        let state = State {
            identifier_refs,
            expressions,
            statements,
            scope_stack: vec![Scope::new()],
            function_symbols: Default::default(),
            struct_symbols: Default::default(),
            diagnostics: Default::default(),
            resolution: Resolution {
                identifiers: BiHashMap::from_iter(
                    identifiers.into_iter().map(|(str, ident)| (ident, str)),
                ),
                identifier_refs: VecMap::with_reserved_capacity(ident_ref_count),
                symbols,
                stmt_symbols: Default::default(),
                types,
                expressions: VecMap::with_reserved_capacity(expr_count),
                statements: VecMap::with_reserved_capacity(stmt_count),
                root,
            },
            invalid_type_id,
            void_type_id,
            none_type_id,
            boolean_type_id,
            number_type_id,
            not_found_symbol_id,
        };

        let mut state = state;
        for native in natives.into_iter() {
            match native {
                Native::Fn(native) => {
                    let ident = state.find_ident_id_by_str(native.name);
                    let parameters = native
                        .kind
                        .signature()
                        .0
                        .iter()
                        .map(|t| state.find_type_id_by_type(t))
                        .collect::<Vec<TypeId>>();
                    let ret_type = state.find_type_id_by_type(&native.kind.signature().1);
                    let fn_type_id =
                        state.insert_type(Type::Function(parameters.clone(), ret_type));

                    state.insert_symbol(
                        ident,
                        SymbolKind::Native(ident, parameters, ret_type, native.kind),
                        fn_type_id,
                    );
                }
                Native::Type(native) => {
                    let id = state.find_ident_id_by_str(native.name);
                    state.insert_symbol(
                        id,
                        SymbolKind::NativeType(id, native.ty.clone()),
                        state.none_type_id,
                    );
                }
            }
        }

        let root = state.resolution.root.clone();
        state.insert_structs(&root);
        state.insert_functions(&root);
        // state.resolution.unreachable.dedup();
        let (_, state) = self.visit_statements(state, &root);

        if !state.diagnostics.is_empty() {
            return Err(state.diagnostics);
        }

        let result = Output {
            identifiers: VecMap::from_iter(state.resolution.identifiers),
            identifier_refs: state.resolution.identifier_refs,
            symbols: state.resolution.symbols,
            types: state
                .resolution
                .types
                .into_iter()
                .map(|(a, b)| (b, a))
                .collect::<VecMap<_, _>>(),
            expressions: state.resolution.expressions,
            statements: state.resolution.statements,
            root,
        };

        debug_assert!(
            !result.identifier_refs.has_holes(),
            "identifier_refs has holes"
        );
        debug_assert!(!result.expressions.has_holes(), "expressions has holes");
        debug_assert!(!result.statements.has_holes(), "statements has holes");
        debug_assert!(!result.symbols.has_holes(), "symbols has holes");
        debug_assert!(!result.types.has_holes(), "types has holes");
        debug_assert!(
            state.identifier_refs.is_empty(),
            "identifier_refs is not empty"
        );
        debug_assert!(state.expressions.is_empty(), "expressions is not empty");
        debug_assert!(state.statements.is_empty(), "statements is not empty");
        debug_assert!(
            ident_ref_count <= result.identifier_refs.len(),
            "ident_ref count does not match"
        );
        debug_assert!(
            expr_count == result.expressions.len(),
            "expr count does not match"
        );
        debug_assert!(
            stmt_count == result.statements.len(),
            "stmt count does not match"
        );

        Ok(result)
    }

    fn visit_expression(&self, mut state: State, expr_id: ExprId) -> (TypeId, State) {
        if let Some(expr) = state.resolution.expressions.get(expr_id) {
            return (expr.resolved_type_id(), state);
        }

        let expr = state
            .expressions
            .remove(expr_id)
            .expect("expr is not resolved");

        if self.unreachable.contains(&expr_id) {
            state
                .resolution
                .expressions
                .insert(expr.id, expr.typed(state.void_type_id));
            return (state.void_type_id, state);
        }

        let (type_id, mut state) = match &expr.kind {
            ExpressionKind::Assignment(Target::Direct(ident_ref), expr) => {
                self.visit_assignment(state, *ident_ref, *expr)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                let (lhs_type_id, new_state) = self.visit_expression(state, *lhs_expr_id);
                let (rhs_type_id, new_state) = self.visit_expression(new_state, *rhs_expr_id);
                state = new_state;

                if lhs_type_id == state.invalid_type_id {
                    return (lhs_type_id, state);
                }
                if rhs_type_id == state.invalid_type_id {
                    return (rhs_type_id, state);
                }

                if lhs_type_id != rhs_type_id {
                    state.diagnostics.report_err(
                        format!(
                            "RSH expected to be of type {}, got {}",
                            state.find_type_by_type_id(lhs_type_id),
                            state.find_type_by_type_id(rhs_type_id)
                        ),
                        state.resolution.expressions[*rhs_expr_id].span.clone(),
                        (file!(), line!()),
                    );
                    return (state.invalid_type_id, state);
                }

                (rhs_type_id, state)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(state, *cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => self.visit_literal(state, literal.kind.clone()),
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                let ident_ref = state
                    .identifier_refs
                    .remove(*ident_ref_id)
                    .expect("ident_ref exists");

                let (expr_type_id, new_state) = self.visit_expression(state, *expr_id);
                state = new_state;

                let ty = state.find_type_by_type_id(expr_type_id);
                let field_type_id = match ty {
                    Type::Struct(stmt_id) => match &state.resolution.statements[*stmt_id].kind {
                        StatementKind::Struct(ident, fields) => {
                            match fields
                                .iter()
                                .enumerate()
                                .find(|(_, field)| field.identifier.id == ident_ref.ident.id)
                            {
                                Some((index, field)) => {
                                    let field_symbol_id = state
                                        .find_symbol_id_for_struct_field(*stmt_id, index)
                                        .expect("field exists");
                                    let ident_ref = ident_ref.resolved(field_symbol_id);
                                    state
                                        .resolution
                                        .identifier_refs
                                        .insert(ident_ref.id, ident_ref);
                                    field.resolved_type_id()
                                }
                                None => {
                                    state.diagnostics.report_err(
                                        format!(
                                            "No field '{}' found in struct {}",
                                            state
                                                .resolution
                                                .identifiers
                                                .get_by_left(&ident_ref.ident.id)
                                                .unwrap(),
                                            state
                                                .resolution
                                                .identifiers
                                                .get_by_left(&ident.id)
                                                .unwrap()
                                        ),
                                        ident_ref.ident.span.clone(),
                                        (file!(), line!()),
                                    );
                                    let ident_ref = ident_ref.resolved(state.not_found_symbol_id);
                                    state
                                        .resolution
                                        .identifier_refs
                                        .insert(ident_ref.id, ident_ref);
                                    state.invalid_type_id
                                }
                            }
                        }
                        _ => panic!("struct expected"),
                    },
                    _ => {
                        state.diagnostics.report_err(
                            format!("Expected struct type, got {}", ty),
                            state.resolution.expressions[*expr_id].span.clone(),
                            (file!(), line!()),
                        );

                        // this it not always true (the left hand side can be a symbol), but it not
                        // being a struct field anyway, considering we did not find any symbol is
                        // (probably) fine...
                        let ident_ref = ident_ref.resolved(state.not_found_symbol_id);
                        state
                            .resolution
                            .identifier_refs
                            .insert(ident_ref.id, ident_ref);
                        state.invalid_type_id
                    }
                };

                (field_type_id, state)
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(state, *ident_ref, params.clone().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.visit_while(state, *cond, *expr),
            ExpressionKind::Block(stmts) => self.visit_block(state, &stmts.clone()),
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                self.visit_struct_instantiation(state, *ident_ref_id, fields, &expr.span)
            }
        };

        state
            .resolution
            .expressions
            .insert(expr_id, expr.typed(type_id));

        (type_id, state)
    }

    fn visit_assignment(
        &self,
        state: State,
        ident_ref: IdentRefId,
        expr: ExprId,
    ) -> (TypeId, State) {
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

        // todo some things to check:
        //  - assign to a let fn

        let (rhs_type_id, mut state) = self.visit_expression(state, expr);

        let lhs_type_id = state
            // todo: to search for method, we need to extract the parameter types from the
            //  expr_type, if it corresponds to a function type. We don't have this
            //  information yet and thus we cannot assign to a variable holding a function
            //  (yet).
            .resolve_ident_ref(ident_ref, None)
            .map(|s| state.resolution.symbols[s].type_id)
            .unwrap_or(state.invalid_type_id);

        if lhs_type_id == state.invalid_type_id {
            return (lhs_type_id, state);
        }

        if rhs_type_id == state.invalid_type_id {
            return (rhs_type_id, state);
        }

        if rhs_type_id != lhs_type_id {
            state.diagnostics.report_err(
                format!(
                    "RSH expected to be of type {}, got {}",
                    state.find_type_by_type_id(lhs_type_id),
                    state.find_type_by_type_id(rhs_type_id)
                ),
                state.resolution.expressions[expr].span.clone(),
                (file!(), line!()),
            );
            return (state.invalid_type_id, state);
        }

        (rhs_type_id, state)
    }

    fn visit_if(
        &self,
        state: State,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> (TypeId, State) {
        let (cond_type, mut state) = self.visit_expression(state, cond);

        if cond_type != state.boolean_type_id && cond_type != state.invalid_type_id {
            state.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    state.find_type_by_type_id(cond_type)
                ),
                state.resolution.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        let (true_branch_type_id, state) = self.visit_expression(state, true_branch);
        let (false_branch_type_id, mut state) = match false_branch {
            None => (state.void_type_id, state),
            Some(e) => self.visit_expression(state, e),
        };

        let true_branch_type = state.find_type_by_type_id(true_branch_type_id);
        let false_branch_type = state.find_type_by_type_id(false_branch_type_id);

        let if_type_id = match (true_branch_type, false_branch_type) {
            (Type::Invalid, _) | (_, Type::Invalid) => state.invalid_type_id,
            (Type::None, Type::None) => true_branch_type_id,
            // fixme the following case is not well tested + implement proper error handing
            (Type::None, t) | (t, Type::None) => state.find_type_id_by_type(t),
            (_, Type::Void) | (Type::Void, _) => {
                // todo: option<t>
                state.void_type_id
            }
            (tt, ft) if tt == ft => true_branch_type_id,
            (tt, ft) => {
                let false_branch =
                    &state.resolution.expressions[false_branch.expect("false branch exists")];
                state.diagnostics.report_err(
                    format!("Expected type {tt}, got {ft}"),
                    false_branch.span.clone(),
                    (file!(), line!()),
                );
                state.invalid_type_id
            }
        };

        (if_type_id, state)
    }

    fn visit_literal(&self, mut state: State, literal: LiteralKind) -> (TypeId, State) {
        let literal_type_id = match literal {
            LiteralKind::Boolean(_) => state.boolean_type_id,
            LiteralKind::Number(_) => state.number_type_id,
            LiteralKind::Identifier(ident_ref) => {
                // todo things to check:
                //  - behaviour when target is let fn
                //  - behaviour when target is a native
                // todo resolve function ref, see comment in resolve_assignment
                state
                    .resolve_ident_ref(ident_ref, None)
                    .map(|s| state.resolution.symbols[s].type_id)
                    // fixme must issue a diagnostic when the identifier is not found
                    .unwrap_or(state.invalid_type_id)
            }
        };

        (literal_type_id, state)
    }

    fn visit_function_call(
        &self,
        state: State,
        ident_ref: IdentRefId,
        params: &[ExprId],
    ) -> (TypeId, State) {
        let invalid_type_id = state.invalid_type_id;

        let mut state = state;
        let mut param_types = Vec::with_capacity(params.len());
        for param in params {
            let (param_type, new_state) = self.visit_expression(state, *param);
            state = new_state;
            if param_type != invalid_type_id {
                param_types.push(param_type)
            }
        }

        if param_types.len() != params.len() {
            return (state.invalid_type_id, state);
        }

        let ret_type_id = state
            .resolve_ident_ref(ident_ref, Some(&param_types))
            .map(|s| match &state.resolution.symbols[s].kind {
                SymbolKind::LetFn(_, _, _, ret_type) => *ret_type,
                SymbolKind::Native(_, _, ret_type, _) => *ret_type,
                SymbolKind::NotFound => state.invalid_type_id,
                _ => {
                    // todo better error (diagnostic)
                    panic!("the resolved symbol was not a function")
                }
            })
            .unwrap_or(state.invalid_type_id);

        (ret_type_id, state)
    }

    fn visit_while(&self, state: State, cond: ExprId, expr: ExprId) -> (TypeId, State) {
        let (cond_type, mut state) = self.visit_expression(state, cond);

        if cond_type != state.boolean_type_id && cond_type != state.invalid_type_id {
            state.diagnostics.report_err(
                format!(
                    "Condition expected to be of type {}, got {}",
                    Type::Boolean,
                    state.find_type_by_type_id(cond_type)
                ),
                state.resolution.expressions[cond].span.clone(),
                (file!(), line!()),
            );
        }

        self.visit_expression(state, expr)
    }

    fn visit_block(&self, mut state: State, stmts: &[StmtId]) -> (TypeId, State) {
        state.push_scope();

        state.insert_functions(stmts);
        let (stmts_type_id, mut state) = self.visit_statements(state, stmts);

        state.pop_scope();

        (stmts_type_id, state)
    }

    fn visit_struct_instantiation(
        &self,
        mut state: State,
        ident_ref_id: IdentRefId,
        field_exprs: &[(IdentRefId, ExprId)],
        span: &Span,
    ) -> (TypeId, State) {
        let mut expr_type_ids = Vec::with_capacity(field_exprs.len());
        for (_, field_expr_id) in field_exprs {
            let (expr_type_id, new_state) = self.visit_expression(state, *field_expr_id);
            state = new_state;
            expr_type_ids.push(expr_type_id);
        }
        debug_assert!(expr_type_ids.len() == field_exprs.len());

        let struct_def = state
            .resolve_ident_ref(ident_ref_id, None)
            .map(|sid| &state.resolution.symbols[sid])
            .and_then(|s| match s.kind {
                SymbolKind::Struct(_, stmt_id) => Some(&state.resolution.statements[stmt_id]),
                _ => None,
            })
            .map(|s| match &s.kind {
                StatementKind::Struct(struct_identifier, struct_fields) => {
                    (s.id, struct_identifier, struct_fields)
                }
                _ => panic!("must be a struct"),
            });

        if let Some((struct_stmt_id, struct_identifier, field_types)) = struct_def {
            if field_exprs.len() != field_types.len() {
                state.diagnostics.report_err(
                    "Struct fields differ in length",
                    span.clone(),
                    (file!(), line!()),
                );
            }

            for ((field_ident_ref_id, field_expr_id), expr_type_id) in
                field_exprs.iter().zip(expr_type_ids.into_iter())
            {
                let field_ident_ref = state
                    .identifier_refs
                    .remove(*field_ident_ref_id)
                    .expect("field ident_ref exists");

                if let Some((index, field)) = field_types
                    .iter()
                    .enumerate()
                    .find(|(_, field)| field.identifier.id == field_ident_ref.ident.id)
                {
                    let field_symbol_id = state
                        .find_symbol_id_for_struct_field(struct_stmt_id, index)
                        .expect("symbol exists");

                    state.resolution.identifier_refs.insert(
                        *field_ident_ref_id,
                        field_ident_ref.resolved(field_symbol_id),
                    );

                    if expr_type_id != field.resolved_type_id() {
                        state.diagnostics.report_err(
                            format!(
                                "Invalid type for field '{}': expected {}, got {}",
                                state
                                    .resolution
                                    .identifiers
                                    .get_by_left(&field.identifier.id)
                                    .unwrap(),
                                state.find_type_by_type_id(field.resolved_type_id()),
                                state.find_type_by_type_id(expr_type_id)
                            ),
                            state.resolution.expressions[*field_expr_id].span.clone(),
                            (file!(), line!()),
                        )
                    }
                } else {
                    // the field was not found by its name...
                    state.resolution.identifier_refs.insert(
                        *field_ident_ref_id,
                        field_ident_ref.resolved(state.not_found_symbol_id),
                    );
                }
            }

            (
                state
                    .find_type_id_by_identifier(struct_identifier.id)
                    .expect("type exists"),
                state,
            )
        } else {
            (state.invalid_type_id, state)
        }
    }

    // todo think about passing the Statement directly
    fn visit_statements(&self, mut state: State, stmts: &[StmtId]) -> (TypeId, State) {
        let mut ret_type = state.void_type_id;

        for &stmt_id in stmts {
            let stmt_type = if let Some(stmt) = state.statements.remove(stmt_id) {
                let (ty, new_state) = self.visit_statement(state, stmt);
                state = new_state;
                ty
            } else {
                let stmt = state
                    .resolution
                    .statements
                    .get(stmt_id)
                    .expect("no unbound statement found");
                match &stmt.kind {
                    StatementKind::Expression(e) => state
                        .resolution
                        .expressions
                        .get(*e)
                        .expect("expression was visited")
                        .resolved_type_id(),
                    StatementKind::Let(..) => state.void_type_id,
                    StatementKind::Ret(..) => state.none_type_id,
                    StatementKind::LetFn(..) => state.void_type_id,
                    StatementKind::Struct(..) => state.void_type_id,
                }
            };

            if ret_type != state.none_type_id {
                ret_type = stmt_type
            }
        }

        (ret_type, state)
    }

    fn visit_statement(
        &self,
        mut state: State,
        stmt: Statement<Untyped, Unbound>,
    ) -> (TypeId, State) {
        let stmt_id = stmt.id;
        let span = stmt.span.clone();

        match stmt.kind {
            StatementKind::Expression(expr) => {
                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Expression(expr), span),
                );

                self.visit_expression(state, expr)
            }
            StatementKind::Let(ident, expr) => {
                let (ident, mut state) = self.visit_let(state, stmt_id, ident, expr);

                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Let(ident, expr), span),
                );

                (state.void_type_id, state)
            }
            StatementKind::Ret(expr, ret_mode) => {
                state = self.visit_expression(state, expr).1;

                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Ret(expr, ret_mode), span),
                );

                (state.none_type_id, state)
            }
            StatementKind::LetFn(ident, params, ret_type, expr) => {
                let (res, mut state) =
                    self.visit_function(state, stmt_id, (ident, params, ret_type), expr, &span);

                if let Ok((identifier, parameters, ret_type)) = res {
                    state.resolution.statements.insert(
                        stmt_id,
                        Statement::new(
                            stmt_id,
                            StatementKind::LetFn(identifier, parameters, ret_type, expr),
                            span,
                        ),
                    );
                }

                (state.void_type_id, state)
            }
            StatementKind::Struct(ident, fields) => {
                let (ident, fields, mut state) = self.visit_struct(state, stmt_id, ident, fields);

                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Struct(ident, fields), span),
                );

                (state.void_type_id, state)
            }
        }
    }

    fn visit_let(
        &self,
        state: State,
        stmt: StmtId,
        ident: Identifier<Unbound>,
        expr: ExprId,
    ) -> (Identifier<Bound>, State) {
        let (expr_type_id, mut state) = self.visit_expression(state, expr);

        if expr_type_id == state.none_type_id {
            let expr = &state.resolution.expressions[expr];
            state.diagnostics.report_err(
                format!("Expected some type, got {}", Type::None),
                expr.span.clone(),
                (file!(), line!()),
            );
        }

        let symbol_id =
            state.insert_symbol(ident.id, SymbolKind::Let(ident.id, stmt), expr_type_id);

        (ident.bind(symbol_id), state)
    }

    fn visit_function(
        &self,
        mut state: State,
        stmt_id: StmtId,
        (ident, params, ret_type): Function<Untyped, Unbound>,
        expr: ExprId,
        span: &Span,
    ) -> (Result<Function<Typed, Bound>, ()>, State) {
        state.push_scope();

        // fixme manage duplicate functions (for whatever it means ... - at least same name same
        //   first parameter type)

        let symbol_id = *state
            .function_symbols
            .get(&stmt_id)
            .expect("function was inserted");

        let (param_types, ret_type_id) = state.resolution.symbols[symbol_id].as_function();
        let param_types = param_types.clone();

        #[cfg(test)]
        println!(
            "Visiting function {name} ({symbol_id:?}) with return type {ret_type}",
            name = state.resolution.identifiers.get_by_left(&ident.id).unwrap(),
            ret_type = state.resolution.types.get_by_right(&ret_type_id).unwrap()
        );

        let mut success = ret_type_id != state.invalid_type_id;

        let params_len = params.len();
        let parameters = params
            .into_iter()
            .zip(param_types)
            .enumerate()
            .filter_map(|(index, (parameter, type_id))| {
                let ident_id = parameter.identifier.id;
                let symbol_kind = SymbolKind::Parameter(ident_id, stmt_id, index);

                if state.symbol_exists(ident_id, &symbol_kind) {
                    state.diagnostics.report_err(
                        format!(
                            "Parameter '{ident}' is already defined",
                            ident = state.resolution.identifiers.get_by_left(&ident_id).unwrap(),
                        ),
                        parameter.identifier.span.clone(),
                        (file!(), line!()),
                    );
                    None
                } else {
                    let symbol_id = state.insert_symbol(ident_id, symbol_kind, type_id);

                    Some(parameter.bind(type_id, symbol_id))
                }
            })
            .collect::<Vec<Parameter<Typed, Bound>>>();

        success = success && parameters.len() == params_len;

        // we want to visit the expression, hence no short-circuit
        let (expr_type_id, mut state) = self.visit_expression(state, expr);
        success = expr_type_id != state.invalid_type_id && success;

        if ret_type_id != state.invalid_type_id {
            let exit_points = self
                .exit_points
                .get(&expr)
                .expect("exit points is computed");

            #[cfg(test)]
            println!(
                "Exit points of {name} ({expr:?}): {exit_points:?}",
                name = state.resolution.identifiers.get_by_left(&ident.id).unwrap(),
            );

            if exit_points.is_empty() {
                if ret_type_id != state.void_type_id {
                    state.diagnostics.report_err(
                        format!(
                            "Function {name} expected to return type {ret_type}, got void",
                            name = state.resolution.identifiers.get_by_left(&ident.id).unwrap(),
                            ret_type = state.resolution.types.get_by_right(&ret_type_id).unwrap()
                        ),
                        span.clone(),
                        (file!(), line!()),
                    );
                }
            } else {
                for exit_point in exit_points.iter() {
                    let (exit_expr_id, explicit) = match exit_point {
                        ExitPoint::Explicit(e) => (*e, true),
                        ExitPoint::Implicit(e) => (*e, false),
                    };

                    let (expr_type_id, new_state) = self.visit_expression(state, exit_expr_id);
                    state = new_state;

                    if expr_type_id == state.invalid_type_id {
                        // nothing to report, that was reported already
                    } else if expr_type_id == state.none_type_id {
                        panic!("functions must not return {}", Type::None)
                    } else if expr_type_id != ret_type_id
                        && (ret_type_id != state.void_type_id || explicit)
                    {
                        let expr = &state.resolution.expressions[exit_expr_id];
                        let expr_type = state.find_type_by_type_id(expr_type_id);

                        state.diagnostics.report_err(
                            format!(
                                "Function {name} expected to return type {ret_type}, got {expr_type}",
                                name = state.resolution.identifiers.get_by_left(&ident.id).unwrap(),
                                ret_type =
                                    state.resolution.types.get_by_right(&ret_type_id).unwrap()
                            ),
                            expr.span.clone(),
                            (file!(), line!()),
                        );
                    }
                }
            }
        }

        state.pop_scope();

        if success {
            if let Some(symbol_id) = state.find_symbol_id_by_ident_and_param_types(
                ident.id,
                Some(
                    &parameters
                        .iter()
                        .map(|p| p.resolved_type_id())
                        .collect::<Vec<TypeId>>(),
                ),
            ) {
                return (
                    Ok((
                        ident.bind(symbol_id),
                        parameters,
                        ret_type.typed(ret_type_id),
                    )),
                    state,
                );
            }
        }

        (Err(()), state)
    }

    fn visit_struct(
        &self,
        mut state: State,
        stmt_id: StmtId,
        identifier: Identifier<Unbound>,
        fields: Vec<Field<Untyped, Unbound>>,
    ) -> (Identifier<Bound>, Vec<Field<Typed, Bound>>, State) {
        let fields = fields
            .into_iter()
            .map(|field| {
                let type_identifier = &state.resolution.identifier_refs[field.ty].ident;

                let ty = state
                    .find_type_id_by_identifier(type_identifier.id)
                    .unwrap_or(state.invalid_type_id);

                field.typed(ty)
            })
            .collect::<Vec<Field<Typed, Unbound>>>();

        let fields = fields
            .into_iter()
            .enumerate()
            .map(|(index, field)| {
                let ident_id = field.identifier.id;
                let symbol_kind = SymbolKind::Field(ident_id, stmt_id, index);

                if state.symbol_exists(ident_id, &symbol_kind) {
                    state.diagnostics.report_err(
                        format!(
                            "Field '{ident}' is already defined",
                            ident = state.resolution.identifiers.get_by_left(&ident_id).unwrap(),
                        ),
                        field.identifier.span.clone(),
                        (file!(), line!()),
                    );
                    field.bind(state.not_found_symbol_id)
                } else {
                    let symbol_id =
                        state.insert_symbol(ident_id, symbol_kind, field.resolved_type_id());
                    field.bind(symbol_id)
                }
            })
            .collect::<Vec<Field<Typed, Bound>>>();

        let symbol_id = state
            .struct_symbols
            .get(&stmt_id)
            .cloned()
            // todo same handling as for visit_function: if not found, return Err()
            //   or, return not_found_symbol_id in visit_function. This requires that the find_*()
            //   and resolve_*() function are reworked...
            // it may happen that the struct is not found in case of duplicate def.
            .unwrap_or(state.not_found_symbol_id);

        (identifier.bind(symbol_id), fields, state)
    }
}

struct State {
    // in
    identifier_refs: VecMap<IdentRefId, IdentifierRef<Unbound>>,
    expressions: VecMap<ExprId, Expression<Untyped>>,
    statements: VecMap<StmtId, Statement<Untyped, Unbound>>,

    // work
    scope_stack: Vec<Scope>,
    /// maps functions (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    function_symbols: HashMap<StmtId, SymbolId>,
    /// maps structs (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    struct_symbols: HashMap<StmtId, SymbolId>,

    // out
    diagnostics: Diagnostics,
    resolution: Resolution,

    // cache
    invalid_type_id: TypeId,
    void_type_id: TypeId,
    none_type_id: TypeId,
    boolean_type_id: TypeId,
    number_type_id: TypeId,
    not_found_symbol_id: SymbolId,
}

impl State {
    /// Resolves an identifier ref by its `IdentRefId` and returns the corresponding `SymbolId`.
    /// The resolution starts in the current scope and crawls the scopes stack up until the
    /// identifier is found.
    fn resolve_ident_ref(
        &mut self,
        ident_ref_id: IdentRefId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId> {
        if let Some(ident_ref) = &self.resolution.identifier_refs.get(ident_ref_id) {
            return Some(ident_ref.resolved_symbol_id());
        }

        let ident_ref = self
            .identifier_refs
            .remove(ident_ref_id)
            .expect("ident_ref is not resolved");

        let ident_id = ident_ref.ident.id;
        match self.find_symbol_id_by_ident_and_param_types(ident_id, param_types) {
            Some(s) => {
                self.resolution
                    .identifier_refs
                    .insert(ident_ref.id, ident_ref.resolved(s));
                Some(s)
            }
            None => {
                // todo nice to have: propose known alternatives
                if let Some(param_types) = param_types {
                    // todo move that to caller side
                    self.diagnostics.report_err(
                        format!(
                            "No function '{}' found for parameters of types ({})",
                            self.resolution.identifiers.get_by_left(&ident_id).unwrap(),
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
                } else {
                    // todo move that to caller side
                    self.diagnostics.report_err(
                        format!(
                            "Identifier '{}' not found",
                            self.resolution.identifiers.get_by_left(&ident_id).unwrap()
                        ),
                        ident_ref.ident.span.clone(),
                        (file!(), line!()),
                    );
                }

                // still, resolve it to an unknown symbol
                self.resolution
                    .identifier_refs
                    .insert(ident_ref.id, ident_ref.resolved(self.not_found_symbol_id));

                None
            }
        }
    }

    /// Resolves an identifier by its `IdentId` and returns the corresponding `SymbolId`. The
    /// resolution starts in the current scope and crawls the scopes stack up until the identifier
    /// is found.
    fn find_symbol_id_by_ident_and_param_types(
        &self,
        ident: IdentId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId> {
        self.scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&self.resolution.symbols, &ident, param_types))
    }

    fn find_symbol_id_for_struct_field(&self, stmt_id: StmtId, index: usize) -> Option<SymbolId> {
        self.resolution
            .stmt_symbols
            .get(&(stmt_id, index))
            .and_then(|sid| self.resolution.symbols.get(*sid))
            .and_then(|s| match s.kind {
                SymbolKind::Field(_, _, _) => Some(s.id),
                _ => None,
            })
    }

    fn insert_functions(&mut self, stmts: &[StmtId]) {
        // first, we resolve all the identifier refs for parameter types and return type ...
        let ident_ref_ids = stmts
            .iter()
            .filter_map(|stmt_id| match &self.statements[*stmt_id].kind {
                StatementKind::LetFn(_, params, ret, ..) => {
                    let mut ident_ref_ids =
                        params.iter().map(|p| p.ty).collect::<Vec<IdentRefId>>();

                    if let Some(ident_ref_id) = ret.ret {
                        ident_ref_ids.push(ident_ref_id);
                    }

                    Some(ident_ref_ids)
                }
                _ => None,
            })
            .flatten()
            .collect::<Vec<IdentRefId>>();

        for ident_ref_id in ident_ref_ids.into_iter() {
            self.resolve_ident_ref(ident_ref_id, None);
        }

        // ... then, we proceed with the function
        let functions = stmts
            .iter()
            .filter_map(|stmt_id| match &self.statements[*stmt_id].kind {
                StatementKind::LetFn(ident, params, ret_type, expr_id) => {
                    let parameter_types = params
                        .iter()
                        .map(|p| {
                            let identifier = &self.resolution.identifier_refs[p.ty].ident;

                            self.find_type_id_by_identifier(identifier.id)
                                .unwrap_or(self.invalid_type_id)
                        })
                        .collect::<Vec<TypeId>>();

                    let ret_type_id = ret_type
                        .ret
                        .map(|ident_ref_id| {
                            let identifier = &self.resolution.identifier_refs[ident_ref_id].ident;

                            self.find_type_id_by_identifier(identifier.id)
                                .unwrap_or(self.invalid_type_id)
                        })
                        .unwrap_or(self.void_type_id);

                    Some((
                        ident.clone(),
                        *stmt_id,
                        parameter_types,
                        ret_type_id,
                        *expr_id,
                    ))
                }
                _ => None,
            })
            .collect::<Vec<(Identifier<Unbound>, StmtId, Vec<TypeId>, TypeId, ExprId)>>();

        for (ident, stmt_id, parameter_types, ret_type, _) in functions.into_iter() {
            let fn_type_id = self.insert_type(Type::Function(parameter_types.clone(), ret_type));

            let symbol_id = self.insert_symbol(
                ident.id,
                SymbolKind::LetFn(ident.id, stmt_id, parameter_types, ret_type),
                fn_type_id,
            );

            self.function_symbols.insert(stmt_id, symbol_id);
        }
    }

    fn insert_structs(&mut self, stmts: &[StmtId]) {
        // we start by inserting all the structs we find, so that the types are available from
        // everywhere in the current scope.

        // first, we insert all structs
        let structs = stmts
            .iter()
            .filter_map(|stmt| match &self.statements[*stmt].kind {
                StatementKind::Struct(ident, _) => Some((*stmt, ident.clone())),
                _ => None,
            })
            .collect::<Vec<(StmtId, Identifier<Unbound>)>>();

        for (stmt_id, identifier) in structs.into_iter() {
            let ident_id = identifier.id;
            let symbol_kind = SymbolKind::Struct(ident_id, stmt_id);

            if self.symbol_exists(ident_id, &symbol_kind) {
                self.diagnostics.report_err(
                    format!(
                        "Struct '{ident}' is already defined in scope",
                        ident = self.resolution.identifiers.get_by_left(&ident_id).unwrap(),
                    ),
                    identifier.span.clone(),
                    (file!(), line!()),
                )
            } else {
                let struct_type_id = self.insert_type(Type::Struct(stmt_id));
                let symbol_id = self.insert_symbol(ident_id, symbol_kind, struct_type_id);
                self.struct_symbols.insert(stmt_id, symbol_id);
            }
        }

        // then we resolve their fields types
        let ident_ref_ids = stmts
            .iter()
            .filter_map(|stmt_id| match &self.statements[*stmt_id].kind {
                StatementKind::Struct(_, fields) => {
                    Some(fields.iter().map(|p| p.ty).collect::<Vec<IdentRefId>>())
                }
                _ => None,
            })
            .flatten()
            .collect::<Vec<IdentRefId>>();

        for ident_ref_id in ident_ref_ids.into_iter() {
            self.resolve_ident_ref(ident_ref_id, None);
        }
    }

    /// Returns `true` if a symbol of the same kind already exists in the current scope.
    fn symbol_exists(&self, ident_id: IdentId, kind: &SymbolKind) -> bool {
        match self
            .scope_stack
            .last()
            .expect("current scope exists")
            .symbols
            .get(&ident_id)
        {
            None => false,
            Some(symbols) => symbols
                .iter()
                .map(|s| &self.resolution.symbols[*s])
                .any(|s| {
                    matches!(
                        (&s.kind, kind),
                        (
                            SymbolKind::Parameter(_, _, _),
                            SymbolKind::Parameter(_, _, _)
                        ) | (SymbolKind::Field(_, _, _), SymbolKind::Field(_, _, _))
                            | (SymbolKind::Struct(_, _), SymbolKind::Struct(_, _))
                    )
                }),
        }
    }

    fn insert_symbol(&mut self, ident_id: IdentId, kind: SymbolKind, ty: TypeId) -> SymbolId {
        let symbol_id = SymbolId::from(self.resolution.symbols.len());

        match &kind {
            SymbolKind::Parameter(_, stmt_id, index) | SymbolKind::Field(_, stmt_id, index) => {
                self.resolution
                    .stmt_symbols
                    .insert((*stmt_id, *index), symbol_id);
            }
            _ => (),
        };

        self.resolution.symbols.push(Symbol {
            id: symbol_id,
            kind,
            type_id: ty,
        });

        self.scope_stack
            .last_mut()
            .expect("current scope exists")
            .symbols
            .entry(ident_id)
            .or_default()
            .push(symbol_id);
        symbol_id
    }

    pub fn find_ident_id_by_str(&self, name: &str) -> IdentId {
        *self
            .resolution
            .identifiers
            .get_by_right(name)
            .unwrap_or_else(|| panic!("Identifier {} not found", name))
    }

    /// Inserts a `Type` if it does not already exist and returns its `TypeId`. If the type already
    /// exists, returns it's `TypeId`
    fn insert_type(&mut self, ty: Type) -> TypeId {
        if let Some(id) = self.resolution.types.get_by_left(&ty) {
            *id
        } else {
            let id = TypeId::from(self.resolution.types.len());
            let did_overwrite = self.resolution.types.insert(ty, id).did_overwrite();
            debug_assert!(!did_overwrite);
            id
        }
    }

    fn find_type_id_by_identifier(&self, ident_id: IdentId) -> Option<TypeId> {
        self.find_symbol_id_by_ident_and_param_types(ident_id, None)
            .and_then(|symbol_id| match &self.resolution.symbols[symbol_id].kind {
                SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                SymbolKind::Struct(_, stmt) => {
                    Some(self.find_type_id_by_type(&Type::Struct(*stmt)))
                }
                _ => None,
            })
    }

    fn find_type_id_by_type(&self, ty: &Type) -> TypeId {
        *self
            .resolution
            .types
            .get_by_left(ty)
            .unwrap_or_else(|| panic!("type {ty:?} exists"))
    }

    fn find_type_by_type_id(&self, ty: TypeId) -> &Type {
        self.resolution
            .types
            .get_by_right(&ty)
            .unwrap_or_else(|| panic!("type {ty} exists"))
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
}

pub struct Resolution {
    pub identifiers: BiHashMap<IdentId, String>,
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef<Bound>>,
    pub symbols: VecMap<SymbolId, Symbol>,
    pub stmt_symbols: HashMap<(StmtId, usize), SymbolId>,
    pub types: BiHashMap<Type, TypeId>,
    pub expressions: VecMap<ExprId, Expression<Typed>>,
    pub statements: VecMap<StmtId, Statement<Typed, Bound>>,
    pub root: Vec<StmtId>,
}

pub struct Output {
    pub identifiers: VecMap<IdentId, String>,
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef<Bound>>,
    pub symbols: VecMap<SymbolId, Symbol>,
    pub types: VecMap<TypeId, Type>,
    pub expressions: VecMap<ExprId, Expression<Typed>>,
    pub statements: VecMap<StmtId, Statement<Typed, Bound>>,
    pub root: Vec<StmtId>,
}

struct Scope {
    symbols: HashMap<IdentId, Vec<SymbolId>>,
}

impl Scope {
    fn new() -> Self {
        Self {
            symbols: Default::default(),
        }
    }

    fn find(
        &self,
        all_symbols: &VecMap<SymbolId, Symbol>,
        ident: &IdentId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId> {
        self.symbols.get(ident).and_then(|symbols| {
            symbols
                .iter()
                .rev()
                .find(|s| {
                    let symbol = &all_symbols[**s];
                    match param_types {
                        None => match symbol.kind {
                            // if no params, the symbol cannot be a function
                            SymbolKind::LetFn(_, _, _, _) | SymbolKind::Native(_, _, _, _) => false,
                            // but it can be any of the others
                            SymbolKind::Let(_, _)
                            | SymbolKind::Parameter(_, _, _)
                            | SymbolKind::NativeType(_, _)
                            | SymbolKind::Field(_, _, _)
                            | SymbolKind::Struct(_, _)
                            | SymbolKind::NotFound => true,
                        },
                        Some(param_types) => match &symbol.kind {
                            // not found can be anything
                            SymbolKind::NotFound => true,
                            // if params, the symbol can be a function
                            SymbolKind::LetFn(_, _, parameters, _) => {
                                param_types == parameters.as_slice()
                            }
                            SymbolKind::Native(_, parameters, _, _) => {
                                param_types == parameters.as_slice()
                            }
                            // but is cannot any of the others
                            SymbolKind::Let(_, _)
                            | SymbolKind::Parameter(_, _, _)
                            | SymbolKind::NativeType(_, _)
                            | SymbolKind::Field(_, _, _)
                            | SymbolKind::Struct(_, _) => false,
                        },
                    }
                })
                .copied()
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::natives::Natives;
    use crate::output::xml::XmlWriter;
    use crate::UnresolvedHir;
    use insta::{assert_debug_snapshot, assert_snapshot};
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_core::error::Level;
    use transmute_core::span::Span;

    #[test]
    fn resolve_ref_to_parameter() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("let x(n: number): number = { n; }"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&hir).serialize());
    }

    #[test]
    fn resolve_ref_to_let() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("let x(): number = { let n = 0; n; }"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&hir).serialize());
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("let x() = { } x();"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&hir).serialize());
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new(
                "let x(n: number): number = { while true { ret n; } }",
            ))
            .parse()
            .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&hir).serialize());
    }

    #[test]
    fn resolve_missing_def() {
        let actual_diagnostics =
            UnresolvedHir::from(Parser::new(Lexer::new("let x() = { n; }")).parse().unwrap())
                .resolve(Natives::default())
                .unwrap_err();

        let actual_diagnostics = actual_diagnostics
            .iter()
            .map(|d| (d.message.as_str(), d.span.clone(), d.level))
            .collect::<Vec<(&str, Span, Level)>>();

        let expected_diagnostics = vec![(
            "Identifier 'n' not found",
            Span::new(1, 13, 12, 1),
            Level::Error,
        )];

        assert_eq!(actual_diagnostics, expected_diagnostics);
    }

    #[test]
    fn rebinding() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("let x = true; let x = 1; x + 1;"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();

        assert_snapshot!("rebinding-xml", XmlWriter::new(&hir).serialize());
    }

    #[test]
    fn fibonacci_rec() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new(include_str!(
                "../../../examples/fibonacci_rec.tm"
            )))
            .parse()
            .unwrap(),
        )
        .resolve(Natives::default())
        .unwrap();
        assert_debug_snapshot!(&hir);
    }

    #[test]
    fn bindings_and_types() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("struct S { f: S } let f(a: S, b: S): S { a; }"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::empty())
        .unwrap();
        assert_debug_snapshot!(&hir);
    }

    macro_rules! test_type_error {
        ($name:ident, $src:expr, $error:expr, $span:expr) => {
            #[test]
            fn $name() {
                let actual_diagnostics =
                    UnresolvedHir::from(Parser::new(Lexer::new($src)).parse().unwrap())
                        .resolve(Natives::default())
                        .unwrap_err();

                let actual_diagnostics_str = actual_diagnostics
                    .iter()
                    .map(|d| (d.message.as_str(), d.span.clone(), d.level))
                    .collect::<Vec<(&str, Span, Level)>>();

                let expected_diagnostics = vec![($error, $span, Level::Error)];

                assert_eq!(
                    actual_diagnostics_str, expected_diagnostics,
                    "{}",
                    actual_diagnostics
                );
            }
        };
    }

    macro_rules! test_type_ok {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                UnresolvedHir::from(Parser::new(Lexer::new($src)).parse().unwrap())
                    .resolve(Natives::new())
                    .expect("ok expected");
            }
        };
    }

    test_type_error!(
        let_expr_type_is_void,
        "let x = if true { ret 42; } else { ret 43; };",
        "Expected some type, got no type",
        Span::new(1, 9, 8, 36)
    );

    test_type_error!(
        if_expected_boolean_condition_got_number,
        "if 42 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 4, 3, 2)
    );
    test_type_ok!(if_expected_boolean_condition_got_boolean, "if true {}");
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_binary,
        "if 40 + 2 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 4, 3, 6)
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_unary,
        "if - 42 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 4, 3, 4)
    );
    test_type_error!(
        if_expected_boolean_condition_got_no_type,
        "if if true { ret 42; } else { ret 43; } {}",
        "Condition expected to be of type boolean, got no type",
        Span::new(1, 4, 3, 36)
    );
    test_type_ok!(
        if_expected_boolean_condition_got_boolean_expr,
        "if 42 > 40 {}"
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; if forty_two {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 24, 23, 9)
    );
    test_type_ok!(
        if_expected_boolean_condition_got_boolean_identifier,
        "let t = true; if t {}"
    );
    test_type_error!(
        if_mismatch_branch_types,
        "if true { true; } else { 42; }",
        "Expected type boolean, got number",
        Span::new(1, 24, 23, 7)
    );
    // todo this should rather be of type option<number>
    test_type_error!(
        if_no_false_branch_to_val,
        "let n = 0; n = if true { 42; };",
        "RSH expected to be of type number, got void",
        Span::new(1, 16, 15, 15)
    );
    test_type_ok!(
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
    test_type_ok!(
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
    test_type_ok!(if_no_false_branch, "if true { 42; }");
    test_type_ok!(if_type, "let n = 0 + if true { 42; } else { 0; };");
    test_type_error!(
        if_expected_boolean_condition_got_number_in_else_if,
        "if true {} else if 42 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 20, 19, 2)
    );
    test_type_ok!(if_type_of_else_if, "if true { 42; } else if false { 0; }");
    test_type_error!(
        while_expected_boolean_condition_got_number,
        "while 42 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 7, 6, 2)
    );
    test_type_error!(
        while_expected_boolean_condition_got_no_type,
        "while if true { ret 42; } else { ret 43; } {}",
        "Condition expected to be of type boolean, got no type",
        Span::new(1, 7, 6, 36)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean,
        "while true {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_binary,
        "while 40 + 2 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 7, 6, 6)
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_unary,
        "while - 42 {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 7, 6, 4)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_expr,
        "while 42 > 40 {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; while forty_two {}",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 27, 26, 9)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_identifier,
        "let t = true; while t {}"
    );
    test_type_error!(
        assignment_wrong_type,
        "let forty_two = 42; forty_two = true;",
        "RSH expected to be of type number, got boolean",
        Span::new(1, 33, 32, 4)
    );
    test_type_ok!(
        assignment_correct_type,
        "let forty_two = 0; forty_two = 42;"
    );
    test_type_ok!(
        assignment_to_function_parameter_correct_type,
        "let f(n: number): number = { n = 1; }"
    );
    test_type_error!(
        assignment_to_function_parameter_incorrect_type,
        "let f(n: number): number = { n = true; }",
        "RSH expected to be of type number, got boolean",
        Span::new(1, 34, 33, 4)
    );
    test_type_error!(
        assignment_wrong_type_from_function,
        "let forty_two = 42; let f(): boolean = true; forty_two = f();",
        "RSH expected to be of type number, got boolean",
        Span::new(1, 58, 57, 3)
    );
    test_type_error!(
        assignment_wrong_type_from_void_function,
        "let forty_two = 42; let f() = {} forty_two = f();",
        "RSH expected to be of type number, got void",
        Span::new(1, 46, 45, 3)
    );
    test_type_error!(
        assignment_always_returning_expr,
        "let forty_two = 42; forty_two = if true { ret 42; } else { ret 43; };",
        "RSH expected to be of type number, got no type",
        Span::new(1, 33, 32, 36)
    );
    test_type_ok!(
        assignment_correct_type_from_function,
        "let forty_two = 0; let f(): number = 42; forty_two = f();"
    );
    test_type_ok!(function_is_allowed_to_return_void, "let f() = { 1; }");
    test_type_ok!(function_has_struct_params, "struct S {} let f(s: S) = { }");
    test_type_ok!(
        struct_instantiation,
        "struct S { x: number } let s = S { x: 1 };"
    );
    test_type_ok!(
        function_returns_struct,
        "struct S {} let f(): S = { S { }; }"
    );
    test_type_ok!(
        function_returns_struct_field,
        "struct S { field: number } let f(s: S): number = { s.field; }"
    );
    test_type_ok!(
        access_struct_field_read,
        "struct S { field: boolean } let s = S { field: true }; if s.field { }"
    );
    test_type_ok!(
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

    test_type_ok!(
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
    test_type_error!(
        access_struct_field_read_invalid_type,
        "struct S { field: number } let s = S { field: 1 }; if s.field { }",
        "Condition expected to be of type boolean, got number",
        Span::new(1, 55, 54, 7)
    );
    test_type_ok!(
        access_struct_field_write,
        "struct S { field: number } let s = S { field: 1 }; s.field = 1;"
    );
    test_type_error!(
        access_struct_field_write_wrong_type,
        "struct S { field: number } let s = S { field: 1 }; s.field = false;",
        "RSH expected to be of type number, got boolean",
        Span::new(1, 62, 61, 5)
    );
    test_type_error!(
        function_returns_void_but_expect_struct,
        "struct S {} let f(): S = { }",
        "Function f expected to return type struct, got void",
        Span::new(1, 13, 12, 16)
    );
    test_type_error!(
        struct_unknown,
        "let s = S {};",
        "Identifier 'S' not found",
        Span::new(1, 9, 8, 1)
    );
    test_type_error!(
        struct_length,
        "struct S { x: number } let s = S { };",
        "Struct fields differ in length",
        Span::new(1, 32, 31, 5)
    );
    test_type_error!(
        duplicate_struct_field,
        "struct S { x: number, x: number }",
        "Field 'x' is already defined",
        Span::new(1, 23, 22, 1)
    );
    test_type_error!(
        struct_invalid_field_type,
        "struct S { x: number } let s = S { x: 1 == 1 };",
        "Invalid type for field 'x': expected number, got boolean",
        Span::new(1, 39, 38, 6)
    );
    test_type_error!(
        access_non_struct,
        "1.x;",
        "Expected struct type, got number",
        Span::new(1, 1, 0, 1)
    );
    test_type_error!(
        duplicate_struct,
        "struct S {} struct S {}",
        "Struct 'S' is already defined in scope",
        Span::new(1, 20, 19, 1)
    );
    test_type_error!(
        function_void_cannot_return_number,
        "let f() = { ret 1; }",
        "Function f expected to return type void, got number",
        Span::new(1, 17, 16, 1)
    );
    test_type_error!(
        function_invalid_return_type,
        "let f(): unknown = { }",
        "Identifier 'unknown' not found",
        Span::new(1, 10, 9, 7)
    );
    test_type_error!(
        function_wrong_return_type,
        "let f(): boolean = { true; 42; }",
        "Function f expected to return type boolean, got number",
        Span::new(1, 28, 27, 2)
    );
    test_type_error!(
        function_wrong_return_type_2,
        "let f(): boolean = { }",
        "Function f expected to return type boolean, got void",
        Span::new(1, 1, 0, 22)
    );
    test_type_error!(
        function_wrong_early_return_type,
        "let f(): number = { if false { ret false; } 42; }",
        "Function f expected to return type number, got boolean",
        Span::new(1, 36, 35, 5)
    );
    test_type_ok!(
        function_parameter_returned_correct_type,
        "let f(n: number): number = { n; }"
    );
    test_type_error!(
        function_parameter_returned_wrong_type,
        "let f(n: number): boolean = { n; }",
        "Function f expected to return type boolean, got number",
        Span::new(1, 31, 30, 1)
    );
    test_type_error!(
        function_parameter_invalid_type,
        "let f(n: unknown) = { let a = n + true; }",
        "Identifier 'unknown' not found",
        Span::new(1, 10, 9, 7)
    );
    test_type_error!(
        function_parameter_incorrect_type,
        "let f(n: number) = { let a = n + true; }",
        "No function 'add' found for parameters of types (number, boolean)",
        Span::new(1, 32, 31, 1)
    );
    test_type_error!(
        function_parameter_incorrect_arity,
        "let f(n: number, b: boolean) = { f(0); }",
        "No function 'f' found for parameters of types (number)",
        Span::new(1, 34, 33, 1)
    );
    test_type_error!(
        duplicate_function_parameter_name,
        "let f(n: number, n: number) = { }",
        "Parameter 'n' is already defined",
        Span::new(1, 18, 17, 1)
    );
    test_type_error!(
        function_not_found,
        "let f() = { g(); }",
        "No function 'g' found for parameters of types ()",
        Span::new(1, 13, 12, 1)
    );
    test_type_ok!(
        function_invalid_return_type_after_valid_return_type,
        "let f(n: number): number = { ret 41; ret true; }"
    );
    test_type_error!(
        unary_operator_invalid_type,
        "let n = - true;",
        "No function 'neg' found for parameters of types (boolean)",
        Span::new(1, 9, 8, 1)
    );
    test_type_error!(
        unary_operator_no_type,
        "let n = - if true { ret 42; } else { ret 43; };",
        "No function 'neg' found for parameters of types (no type)",
        Span::new(1, 9, 8, 1)
    );
    test_type_error!(
        call_variable,
        "let n = 10; n();",
        "No function 'n' found for parameters of types ()",
        Span::new(1, 13, 12, 1)
    );
    // fixme un-comment the following tests
    // test_type_ok!(
    //     unreachable_statement1,
    //     r#"
    //     let f(n: number): number = {
    //         if n == 42 {
    //             let m = 0;
    //             ret m + 1;
    //         } else {
    //             let m = 0;
    //             ret m - 1;
    //         };
    //         ret f(42);
    //     }
    //     "#
    // );
    // test_type_ok!(
    //     unreachable_statement1,
    //     r#"
    //     let f(n: number): number = {
    //         while n != 42 {
    //             ret n;
    //         }
    //         ret n;
    //     }
    //     "#
    // );
    test_type_ok!(
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
    // fixme un-comment the following test
    // test_type_ok!(
    //     assign_from_native,
    //     "let n = add;"
    // );
    test_type_ok!(nested_function_same_type, "let f() { let g() {} }");
    test_type_ok!(
        nested_function_different_types,
        "let f(): number { let g(): boolean { true; }; 1; }"
    );

    // fixme un-comment the following test
    // test_type_ok!(
    //     struct_same_field_name,
    //     r#"
    //     struct Inner { field: number };
    //     struct Outer { field: Inner };
    //     "#
    // );
    // fixme un-comment the following test
    // test_type_ok!(
    //     struct_instantiation_same_field_name,
    //     r#"
    //     struct Inner { field: number };
    //     struct Outer { field: Inner };
    //     let s = Outer { field: Inner { field: 1 } };
    //     "#
    // );
}
