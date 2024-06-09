use crate::ast::expression::{Expression, ExpressionKind, Typed, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{Bound, IdentifierRef, Unbound};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::literal::LiteralKind;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::{Field, Parameter, Return, Statement, StatementKind};
use crate::error::{Diagnostic, Diagnostics};
use crate::exit_points;
use crate::exit_points::{ExitPoint, ExitPoints};
use crate::interpreter::Value;
use crate::lexer::Span;
use crate::natives::{Native, Natives};
use crate::vec_map::VecMap;
use bimap::BiHashMap;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};

pub struct Resolver {}

type BoundParametersAndReturnType = (Vec<Parameter<Bound>>, Return<Bound>);

impl Resolver {
    pub fn new() -> Self {
        Self {}
    }

    pub fn resolve(
        &self,
        identifiers: VecMap<IdentId, String>,
        identifier_refs: VecMap<IdentRefId, IdentifierRef<Unbound>>,
        expressions: VecMap<ExprId, Expression<Untyped>>,
        statements: VecMap<StmtId, Statement<Unbound>>,
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
            ty: invalid_type_id,
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
            diagnostics: Default::default(),
            resolution: Resolution {
                identifiers: VecMap::from_iter(identifiers.into_iter().map(|(a, b)| (b, a))),
                identifier_refs: VecMap::with_reserved_capacity(ident_ref_count),
                symbols,
                types,
                expressions: VecMap::with_reserved_capacity(expr_count),
                statements: VecMap::with_reserved_capacity(stmt_count),
                root,
                exit_points: Default::default(),
                unreachable: vec![],
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
                    let ident = state.identifier_id(native.name());
                    let parameters = native
                        .parameters()
                        .iter()
                        .map(|t| state.resolve_type_id_by_type(t))
                        .collect::<Vec<TypeId>>();
                    let ret_type = state.resolve_type_id_by_type(native.return_type());
                    let fn_type_id =
                        state.insert_type(Type::Function(parameters.clone(), ret_type));

                    state.insert_symbol(
                        ident,
                        SymbolKind::Native(ident, parameters, ret_type, native.body()),
                        fn_type_id,
                    );
                }
                Native::Type(native) => {
                    let id = state.identifier_id(native.name());
                    state.insert_symbol(
                        id,
                        SymbolKind::NativeType(id, native.ty().clone()),
                        state.none_type_id,
                    );
                }
            }
        }

        let root = state.resolution.root.clone();
        state.insert_structs(&root);
        state.insert_functions(&root);
        state.resolution.unreachable.dedup();
        let (_, state) = self.visit_statements(state, &root);

        if !state.diagnostics.is_empty() {
            return Err(state.diagnostics);
        }

        let result = Output {
            identifiers: state.resolution.identifiers,
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
            exit_points: state.resolution.exit_points,
            unreachable: state.resolution.unreachable,
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
            return (expr.ty_id(), state);
        }

        let expr = state
            .expressions
            .remove(expr_id)
            .expect("expr is not resolved");

        // todo take_kind()
        let (type_id, mut state) = match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                self.visit_assignment(state, *ident_ref, *expr)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(state, *cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => self.visit_literal(state, literal.kind().clone()),
            ExpressionKind::Binary(left, op, right) => {
                return self.visit_binary_operator(
                    state,
                    expr.id(),
                    expr.span().clone(),
                    *left,
                    op.clone(),
                    *right,
                );
            }
            ExpressionKind::Unary(op, operand) => {
                return self.visit_unary_operator(
                    state,
                    expr.id(),
                    expr.span().clone(),
                    op.clone(),
                    *operand,
                )
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(state, *ident_ref, params.clone().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.visit_while(state, *cond, *expr),
            ExpressionKind::Block(stmts) => self.visit_block(state, &stmts.clone()),
            ExpressionKind::Dummy => {
                panic!("must not resolve an invalid AST")
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

        let (expr_type, mut state) = self.visit_expression(state, expr);

        let expected_type = state
            // todo: to search for method, we need to extract the parameter types from the
            //  expr_type, it it corresponds to a function type. We don't have this
            //  information yet and this we cannot assign to a variable holding a function
            //  (yet).
            .resolve_ident_ref(ident_ref, None)
            .map(|s| state.resolution.symbols[s].ty)
            .unwrap_or(state.invalid_type_id);

        if expected_type == state.invalid_type_id {
            return (expected_type, state);
        }

        if expr_type != expected_type {
            state.diagnostics.report_err(
                format!(
                    "Expected type {}, got {}",
                    state.lookup_type(expected_type),
                    state.lookup_type(expr_type)
                ),
                state.resolution.expressions[expr].span().clone(),
                (file!(), line!()),
            );
            return (state.invalid_type_id, state);
        }

        (expr_type, state)
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
                    "Expected type {}, got {}",
                    Type::Boolean,
                    state.lookup_type(cond_type)
                ),
                state.resolution.expressions[cond].span().clone(),
                (file!(), line!()),
            );
        }

        let (true_branch_type_id, state) = self.visit_expression(state, true_branch);
        let (false_branch_type_id, mut state) = match false_branch {
            None => (state.void_type_id, state),
            Some(e) => self.visit_expression(state, e),
        };

        let true_branch_type = state.lookup_type(true_branch_type_id);
        let false_branch_type = state.lookup_type(false_branch_type_id);

        let if_type_id = match (true_branch_type, false_branch_type) {
            (Type::Invalid, _) | (_, Type::Invalid) => state.invalid_type_id,
            (Type::None, Type::None) => true_branch_type_id,
            // fixme the following case is not well tested + implement proper error handing
            (Type::None, t) | (t, Type::None) => state.resolve_type_id_by_type(t),
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
                    false_branch.span().clone(),
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
                    .map(|s| state.resolution.symbols[s].ty)
                    .unwrap_or(state.invalid_type_id)
            }
        };

        (literal_type_id, state)
    }

    fn visit_binary_operator(
        &self,
        state: State,
        expr: ExprId,
        expr_span: Span,
        left: ExprId,
        op: BinaryOperator,
        right: ExprId,
    ) -> (TypeId, State) {
        let (left_type, state) = self.visit_expression(state, left);
        let (right_type, mut state) = self.visit_expression(state, right);

        let ident_id = state.identifier_id(op.kind().function_name());
        let param_types = [left_type, right_type];
        let symbol = match state.resolve_ident(ident_id, Some(&param_types)) {
            None => {
                state.diagnostics.report_err(
                    format!(
                        "No function '{}' found for parameters of types ({}, {})",
                        state.resolution.identifiers[ident_id],
                        state
                            .resolution
                            .types
                            .get_by_right(&param_types[0])
                            .unwrap()
                            .to_string(),
                        state
                            .resolution
                            .types
                            .get_by_right(&param_types[1])
                            .unwrap()
                            .to_string(),
                    ),
                    op.span().clone(),
                    (file!(), line!()),
                );
                state.not_found_symbol_id
            }
            Some(s) => s,
        };

        let ident_ref_id =
            state.create_identifier_ref(Identifier::new(ident_id, op.span().clone()), symbol);
        let parameters = vec![left, right];
        let (ret_type, mut state) = self.visit_function_call(state, ident_ref_id, &parameters);

        // todo keep it here?
        // here, we replace the `left op right` with `op_fn(left, right)` in the ast as a de-sugar
        // action
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, parameters),
            expr_span,
        )
        .typed(ret_type);
        state.resolution.expressions.insert(expr, expression);

        (ret_type, state)
    }

    fn visit_unary_operator(
        &self,
        state: State,
        expr: ExprId,
        expr_span: Span,
        op: UnaryOperator,
        operand: ExprId,
    ) -> (TypeId, State) {
        let (operand_type, mut state) = self.visit_expression(state, operand);

        let ident_id = state.identifier_id(op.kind().function_name());
        let symbol = match state.resolve_ident(ident_id, Some(&[operand_type])) {
            None => {
                state.diagnostics.report_err(
                    format!(
                        "No function '{}' found for parameters of types ({})",
                        state.resolution.identifiers[ident_id],
                        state
                            .resolution
                            .types
                            .get_by_right(&operand_type)
                            .unwrap()
                            .to_string(),
                    ),
                    op.span().clone(),
                    (file!(), line!()),
                );
                state.not_found_symbol_id
            }
            Some(d) => d,
        };

        let ident_ref_id =
            state.create_identifier_ref(Identifier::new(ident_id, op.span().clone()), symbol);
        let parameters = vec![operand];
        let (ret_type, mut state) = self.visit_function_call(state, ident_ref_id, &parameters);

        // todo keep it here?
        // here, we replace the `op operand` with `op_fn(operand)` in the ast as a de-sugar
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, parameters),
            expr_span,
        )
        .typed(ret_type);
        state.resolution.expressions.insert(expr, expression);

        (ret_type, state)
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
            // todo better error (diagnostic)
            return (state.invalid_type_id, state);
        }

        let ret_type_id = state
            .resolve_ident_ref(ident_ref, Some(&param_types))
            .map(|s| match &state.resolution.symbols[s].kind {
                SymbolKind::LetFn(_, _, ret_type) => *ret_type,
                SymbolKind::Native(_, _, ret_type, _) => *ret_type,
                SymbolKind::Let(_)
                | SymbolKind::Parameter(_, _)
                | SymbolKind::NativeType(_, _)
                | SymbolKind::Field(_, _)
                | SymbolKind::Struct(_) => {
                    // todo better error (diagnostic)
                    panic!("the resolved symbol was not a function")
                }
                SymbolKind::NotFound => state.invalid_type_id,
            })
            .unwrap_or(state.invalid_type_id);

        (ret_type_id, state)
    }

    fn visit_while(&self, state: State, cond: ExprId, expr: ExprId) -> (TypeId, State) {
        let (cond_type, mut state) = self.visit_expression(state, cond);

        if cond_type != state.boolean_type_id && cond_type != state.invalid_type_id {
            state.diagnostics.report_err(
                format!(
                    "Expected type {}, got {}",
                    Type::Boolean,
                    state.lookup_type(cond_type)
                ),
                state.resolution.expressions[cond].span().clone(),
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
                match stmt.kind() {
                    StatementKind::Expression(e) => state
                        .resolution
                        .expressions
                        .get(*e)
                        .expect("expression was visited")
                        .ty_id(),
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

    fn visit_statement(&self, mut state: State, stmt: Statement<Unbound>) -> (TypeId, State) {
        let stmt_id = stmt.id();
        let span = stmt.span().clone();

        match stmt.take_kind() {
            StatementKind::Expression(expr) => {
                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Expression(expr), span),
                );

                self.visit_expression(state, expr)
            }
            StatementKind::Let(ident, expr) => {
                state = self.visit_let(state, stmt_id, ident.id(), expr);

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
                let (ret, mut state) =
                    self.visit_function(state, stmt_id, params, ret_type, expr, &span);

                if let Ok((parameters, ret_type)) = ret {
                    state.resolution.statements.insert(
                        stmt_id,
                        Statement::new(
                            stmt_id,
                            StatementKind::LetFn(ident, parameters, ret_type, expr),
                            span,
                        ),
                    );
                }

                (state.void_type_id, state)
            }
            StatementKind::Struct(ident, fields) => {
                let mut state = self.visit_struct(state, stmt_id, &fields);

                state.resolution.statements.insert(
                    stmt_id,
                    Statement::new(stmt_id, StatementKind::Struct(ident, fields), span),
                );

                (state.void_type_id, state)
            }
        }
    }

    fn visit_let(&self, state: State, stmt: StmtId, ident: IdentId, expr: ExprId) -> State {
        let (expr_type_id, mut state) = self.visit_expression(state, expr);

        if expr_type_id == state.none_type_id {
            let expr = &state.resolution.expressions[expr];
            state.diagnostics.report_err(
                format!("Expected some type, got {}", Type::None),
                expr.span().clone(),
                (file!(), line!()),
            );
        }

        state.insert_symbol(ident, SymbolKind::Let(stmt), expr_type_id);
        state
    }

    fn visit_function(
        &self,
        mut state: State,
        stmt: StmtId,
        params: Vec<Parameter<Unbound>>,
        ret_type: Return<Unbound>,
        expr: ExprId,
        span: &Span,
    ) -> (Result<BoundParametersAndReturnType, ()>, State) {
        state.push_scope();

        // fixme we redo the same type computation as in insert_function, but here, we already know
        //   the types.

        let ret_type_id = match ret_type.take_identifier() {
            Some(ident) => {
                match state.resolve_type_id_by_identifier(&ident) {
                    None => {
                        // no need to report error here, it was already reported in insert_functions
                        Err((
                            state.resolve_type_id_by_type(&Type::Void),
                            Return::<Unbound>::none(),
                        ))
                    }
                    Some(ret_type_id) => {
                        let bound = state
                            .resolve_ident(ident.id(), None)
                            .map(Bound)
                            .unwrap_or_else(|| {
                                panic!("symbol for type_id '{}' exists", ret_type_id)
                            });
                        Ok((ret_type_id, Return::some(ident, bound)))
                    }
                }
            }
            None => Ok((state.resolve_type_id_by_type(&Type::Void), Return::none())),
        };

        let mut success = ret_type_id.is_ok();

        let params_len = params.len();
        let parameters = params
            .into_iter()
            .enumerate()
            .filter_map(|(index, parameter)| {
                match state.resolve_type_id_by_identifier(parameter.ty()) {
                    None => {
                        // diagnostic already produced in resolve_type_id_by_identifier
                        // todo we might rather use the illegal type
                        None
                    }
                    Some(type_id) => {
                        let symbol_id = state.insert_symbol(
                            parameter.identifier().id(),
                            SymbolKind::Parameter(stmt, index),
                            type_id,
                        );

                        Some(parameter.bind(symbol_id))
                    }
                }
            })
            .collect::<Vec<Parameter<Bound>>>();

        success = success && parameters.len() == params_len;

        // we want to visit the expression, hence no short-circuit
        let (expr_type_id, mut state) = self.visit_expression(state, expr);
        success = expr_type_id != state.invalid_type_id && success;

        if let Ok((ret_type_id, _)) = ret_type_id {
            // todo we remove it here and put it back later to avoid borrowing issues. can it be
            //   improved? - exit points dont change while we visit the tree => move it outside of
            //   state, maybe?
            let exit_points = state
                .resolution
                .exit_points
                .remove(&expr)
                .expect("exit points is computed");

            if exit_points.is_empty() {
                if ret_type_id != state.void_type_id {
                    state.diagnostics.report_err(
                        format!(
                            "Expected type {ret_type}, got void",
                            ret_type = state.resolution.types.get_by_right(&ret_type_id).unwrap()
                        ),
                        span.clone(),
                        (file!(), line!()),
                    );
                }
            } else {
                for exit_point in exit_points.iter() {
                    let (exit_expr_id, explicit) = match exit_point {
                        ExitPoint::Explicit(e) => (e, true),
                        ExitPoint::Implicit(e) => (e, false),
                    };

                    let (expr_type_id, new_state) = self.visit_expression(state, *exit_expr_id);
                    state = new_state;

                    if expr_type_id == state.invalid_type_id {
                        // nothing to report, that was reported already
                    } else if expr_type_id == state.none_type_id {
                        panic!("functions must not return {}", Type::None)
                    } else if expr_type_id != ret_type_id
                        && (ret_type_id != state.void_type_id || explicit)
                    {
                        let expr = &state.resolution.expressions[*exit_expr_id];
                        let expr_type = state.lookup_type(expr_type_id);

                        state.diagnostics.report_err(
                            format!(
                                "Expected type {ret_type}, got {expr_type}",
                                ret_type =
                                    state.resolution.types.get_by_right(&ret_type_id).unwrap()
                            ),
                            expr.span().clone(),
                            (file!(), line!()),
                        );
                    }
                }
            }

            state.resolution.exit_points.insert(expr, exit_points);
        }

        state.pop_scope();

        let ret = if success {
            Ok((
                parameters,
                ret_type_id.expect("cannot be success if ret_type is err").1,
            ))
        } else {
            Err(())
        };

        (ret, state)
    }

    fn visit_struct(&self, mut state: State, stmt: StmtId, fields: &[Field]) -> State {
        for (index, parameter) in fields.iter().enumerate() {
            let ty = state
                .resolve_type_id_by_identifier(parameter.ty())
                .unwrap_or(state.invalid_type_id);

            state.insert_symbol(
                parameter.identifier().id(),
                SymbolKind::Field(stmt, index),
                ty,
            );
        }

        state
    }
}

struct State {
    // in
    identifier_refs: VecMap<IdentRefId, IdentifierRef<Unbound>>,
    expressions: VecMap<ExprId, Expression<Untyped>>,
    statements: VecMap<StmtId, Statement<Unbound>>,

    // work
    scope_stack: Vec<Scope>,

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
    fn create_identifier_ref(&mut self, identifier: Identifier, symbol: SymbolId) -> IdentRefId {
        let id = IdentRefId::from(self.resolution.identifier_refs.len());
        self.resolution
            .identifier_refs
            .push(IdentifierRef::new_resolved(id, identifier, symbol));
        id
    }

    /// Resolves an identifier ref by its `IdentRefId` and returns the corresponding `SymbolId`.
    /// The resolution starts in the current scope and crawls the scopes stack up until the
    /// identifier is found.
    fn resolve_ident_ref(
        &mut self,
        ident_ref_id: IdentRefId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId> {
        if let Some(ident_ref) = &self.resolution.identifier_refs.get(ident_ref_id) {
            return Some(ident_ref.symbol_id());
        }

        let ident_ref = self
            .identifier_refs
            .remove(ident_ref_id)
            .expect("ident_ref is not resolved");

        let ident_id = ident_ref.ident_id();
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&self.resolution.symbols, &ident_id, param_types))
        {
            Some(s) => {
                self.resolution
                    .identifier_refs
                    .insert(ident_ref.id(), ident_ref.resolved(s));
                Some(s)
            }
            None => {
                // todo nice to have: propose known alternatives
                if let Some(param_types) = param_types {
                    // todo move that to caller side
                    self.diagnostics.report_err(
                        format!(
                            "No function '{}' found for parameters of types ({})",
                            self.resolution.identifiers[ident_id],
                            param_types
                                .iter()
                                .map(|t| self.lookup_type(*t))
                                .map(Type::to_string)
                                .collect::<Vec<String>>()
                                .join(", ")
                        ),
                        ident_ref.ident().span().clone(),
                        (file!(), line!()),
                    );
                } else {
                    // todo move that to caller side
                    self.diagnostics.report_err(
                        format!(
                            "No variable '{}' found",
                            self.resolution.identifiers[ident_id]
                        ),
                        ident_ref.ident().span().clone(),
                        (file!(), line!()),
                    );
                }
                None
            }
        }
    }

    /// Resolves an identifier by its `IdentId` and returns the corresponding `SymbolId`. The
    /// resolution starts in the current scope and crawls the scopes stack up until the identifier
    /// is found.
    // todo add coarse-grained kind of expected symbol (var, callable, type)
    fn resolve_ident(&self, ident: IdentId, param_types: Option<&[TypeId]>) -> Option<SymbolId> {
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&self.resolution.symbols, &ident, param_types))
        {
            Some(s) => Some(s),
            None => {
                // todo nice to have: propose known alternatives
                None
            }
        }
    }

    fn insert_functions(&mut self, stmts: &[StmtId]) {
        let functions = stmts
            .iter()
            .filter_map(|stmt_id| {
                match self.statements[*stmt_id].kind() {
                    StatementKind::LetFn(ident, params, ret_type, expr_id) => {
                        // todo could be moved to its own pass to produce an Ast containing exit
                        //   points and unreachable expressions
                        let exit_points = ExitPoints::new(&self.expressions, &self.statements)
                            .exit_points(*expr_id);

                        let parameter_types = params
                            .iter()
                            .map(|p| {
                                self.resolve_type_id_by_identifier(p.ty()).ok_or_else(|| {
                                    Diagnostic::error(
                                        format!(
                                            "'{}' is not a known type",
                                            self.resolution.identifiers[p.ty().id()]
                                        ),
                                        p.ty().span().clone(),
                                        (file!(), line!()),
                                    )
                                })
                            })
                            .collect::<Vec<Result<TypeId, Diagnostic>>>();

                        let parameter_types = parameter_types
                            .into_iter()
                            .map(|e| match e {
                                Ok(t) => t,
                                Err(d) => {
                                    self.diagnostics.push(d);
                                    self.invalid_type_id
                                }
                            })
                            .collect::<Vec<TypeId>>();

                        let ret_type_id = ret_type
                            .identifier()
                            .map(|ident| match self.resolve_type_id_by_identifier(ident) {
                                None => Err(Diagnostic::error(
                                    format!(
                                        "'{}' is not a known type",
                                        self.resolution.identifiers[ident.id()]
                                    ),
                                    ident.span().clone(),
                                    (file!(), line!()),
                                )),
                                Some(t) => Ok(t),
                            })
                            .unwrap_or(Ok(self.void_type_id));

                        let ret_type_id = match ret_type_id {
                            Ok(t) => t,
                            Err(d) => {
                                self.diagnostics.push(d);
                                self.invalid_type_id
                            }
                        };

                        Some((
                            ident.clone(),
                            *stmt_id,
                            parameter_types,
                            ret_type_id,
                            *expr_id,
                            exit_points,
                        ))
                    }
                    _ => None,
                }
            })
            .collect::<Vec<(
                Identifier,
                StmtId,
                Vec<TypeId>,
                TypeId,
                ExprId,
                exit_points::Output,
            )>>();

        for (ident, stmt_id, parameter_types, ret_type, expr_id, mut exit_points) in
            functions.into_iter()
        {
            let fn_type_id = self.insert_type(Type::Function(parameter_types.clone(), ret_type));

            self.insert_symbol(
                ident.id(),
                SymbolKind::LetFn(stmt_id, parameter_types, ret_type),
                fn_type_id,
            );
            self.resolution
                .exit_points
                .insert(expr_id, exit_points.exit_points);
            self.resolution
                .unreachable
                .append(&mut exit_points.unreachable);
        }
    }

    fn insert_structs(&mut self, stmts: &[StmtId]) {
        // we start by inserting all the structs we find, so that the types are available from
        // everywhere in the current scope.

        let structs = stmts
            .iter()
            .filter_map(|stmt| match self.statements[*stmt].kind() {
                StatementKind::Struct(ident, _) => Some((*stmt, ident.id())),
                _ => None,
            })
            .collect::<Vec<(StmtId, IdentId)>>();

        for (stmt_id, ident_id) in structs.into_iter() {
            let struct_type_id = self.insert_type(Type::Struct(stmt_id));
            // todo this is not really the struct type ... weird
            self.insert_symbol(ident_id, SymbolKind::Struct(stmt_id), struct_type_id);
        }
    }

    fn insert_symbol(&mut self, ident: IdentId, kind: SymbolKind, ty: TypeId) -> SymbolId {
        let id = SymbolId::from(self.resolution.symbols.len());
        self.resolution.symbols.push(Symbol { id, kind, ty });
        self.scope_stack
            .last_mut()
            .expect("current scope exists")
            .symbols
            .entry(ident)
            .or_default()
            .push(id);
        id
    }

    pub fn identifier_id(&self, name: &str) -> IdentId {
        // todo use a map instead
        for (id, ident) in self.resolution.identifiers.iter() {
            if ident == name {
                return id;
            }
        }
        panic!("Identifier {} not found", name)
    }

    /// Inserts a `Type` if it does not already exist and returns its `TypeId`. If the type already
    /// exists, returns it's `TypeId`
    fn insert_type(&mut self, ty: Type) -> TypeId {
        if let Some(id) = self.resolution.types.get_by_left(&ty) {
            *id
        } else {
            let id = TypeId::from(self.resolution.types.len());
            debug_assert!(!self.resolution.types.insert(ty, id).did_overwrite());
            id
        }
    }

    // todo make it take IdentId
    fn resolve_type_id_by_identifier(&self, ident: &Identifier) -> Option<TypeId> {
        match self.resolve_ident(ident.id(), None) {
            None => None,
            Some(s) => {
                let symbol = &self.resolution.symbols[s];
                match &symbol.kind {
                    SymbolKind::NativeType(_, ty) => Some(self.resolve_type_id_by_type(ty)),
                    SymbolKind::Struct(stmt) => {
                        Some(self.resolve_type_id_by_type(&Type::Struct(*stmt)))
                    }
                    _ => None,
                }
            }
        }
    }

    fn resolve_type_id_by_type(&self, ty: &Type) -> TypeId {
        *self
            .resolution
            .types
            .get_by_left(ty)
            .unwrap_or_else(|| panic!("type {ty:?} exists"))
    }

    fn lookup_type(&self, ty: TypeId) -> &Type {
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
    pub identifiers: VecMap<IdentId, String>,
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef<Bound>>,
    pub symbols: VecMap<SymbolId, Symbol>,
    pub types: BiHashMap<Type, TypeId>,
    pub expressions: VecMap<ExprId, Expression<Typed>>,
    pub statements: VecMap<StmtId, Statement<Bound>>,
    pub root: Vec<StmtId>,
    pub exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    pub unreachable: Vec<ExprId>,
}

pub struct Output {
    pub identifiers: VecMap<IdentId, String>,
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef<Bound>>,
    pub symbols: VecMap<SymbolId, Symbol>,
    pub types: VecMap<TypeId, Type>,
    pub expressions: VecMap<ExprId, Expression<Typed>>,
    pub statements: VecMap<StmtId, Statement<Bound>>,
    pub root: Vec<StmtId>,
    pub exit_points: HashMap<ExprId, Vec<ExitPoint>>,
    pub unreachable: Vec<ExprId>,
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
                            SymbolKind::LetFn(_, _, _) | SymbolKind::Native(_, _, _, _) => false,
                            // but it can be any of the others
                            SymbolKind::Let(_)
                            | SymbolKind::Parameter(_, _)
                            | SymbolKind::NativeType(_, _)
                            | SymbolKind::Field(_, _)
                            | SymbolKind::Struct(_)
                            | SymbolKind::NotFound => true,
                        },
                        Some(param_types) => match &symbol.kind {
                            // not found can be anything
                            SymbolKind::NotFound => true,
                            // if params, the symbol can be a function
                            SymbolKind::LetFn(_, ref fn_param_type, _) => {
                                param_types == fn_param_type.as_slice()
                            }
                            SymbolKind::Native(_, parameters, _, _) => {
                                param_types == parameters.as_slice()
                            }
                            // but is cannot any of the others
                            SymbolKind::Let(_)
                            | SymbolKind::Parameter(_, _)
                            | SymbolKind::NativeType(_, _)
                            | SymbolKind::Field(_, _)
                            | SymbolKind::Struct(_) => false,
                        },
                    }
                })
                .copied()
        })
    }
}

#[derive(Debug, PartialEq)]
pub struct Symbol {
    id: SymbolId,
    kind: SymbolKind,
    ty: TypeId,
}

impl Symbol {
    pub fn kind(&self) -> &SymbolKind {
        &self.kind
    }

    pub fn ty(&self) -> TypeId {
        self.ty
    }
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    NotFound,
    Let(StmtId),
    LetFn(StmtId, Vec<TypeId>, TypeId),
    Parameter(StmtId, usize),
    Struct(StmtId),
    Field(StmtId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, fn(Vec<Value>) -> Value),
}

// todo think about it being in Native
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub enum Type {
    /// The type is invalid
    Invalid,

    Boolean,
    Function(Vec<TypeId>, TypeId),
    Struct(StmtId),
    Number,

    /// This value is used when the statement/expression does not have any value. This is the
    /// case for `let` and `let fn`.
    #[default]
    Void,

    /// This value is used when the statement/expression does not return any value. This is the
    /// case for `ret`.
    None,
}

impl Type {
    pub fn identifier(&self) -> &'static str {
        match self {
            Type::Invalid | Type::None | Type::Function(..) | Type::Struct(..) => unimplemented!(),
            Type::Boolean => "boolean",
            Type::Number => "number",
            Type::Void => "void",
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function(..) => write!(f, "function"),
            Type::Struct(..) => write!(f, "struct"),
            Type::Number => write!(f, "number"),
            Type::Void => write!(f, "void"),
            Type::None => write!(f, "no type"),
            Type::Invalid => write!(f, "invalid"),
        }
    }
}

impl TryFrom<&str> for Type {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "boolean" => Ok(Type::Boolean),
            "number" => Ok(Type::Number),
            "void" => Ok(Type::Void),
            &_ => Err(format!("'{}' is not a known type", value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::desugar::ImplicitRetConverter;
    use crate::error::Level;
    use crate::lexer::{Lexer, Span};
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

    #[test]
    fn resolve_ref_to_parameter() {
        let ast = Parser::new(Lexer::new("let x(n: number): number = { n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRetConverter::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_ref_to_let() {
        let ast = Parser::new(Lexer::new("let x(): number = { let n = 0; n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRetConverter::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let ast = Parser::new(Lexer::new("let x() = { } x();"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRetConverter::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let ast = Parser::new(Lexer::new(
            "let x(n: number): number = { while true { ret n; } }",
        ))
        .parse()
        .unwrap()
        .convert_implicit_ret(ImplicitRetConverter::new())
        .resolve(Resolver::new(), Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_missing_def() {
        let actual_diagnostics = Parser::new(Lexer::new("let x() = { n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRetConverter::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap_err();

        let actual_diagnostics = actual_diagnostics
            .iter()
            .map(|d| (d.message(), d.span().clone(), d.level()))
            .collect::<Vec<(&str, Span, Level)>>();

        let expected_diagnostics = vec![(
            "No variable 'n' found",
            Span::new(1, 13, 12, 1),
            Level::Error,
        )];

        assert_eq!(actual_diagnostics, expected_diagnostics);
    }

    #[test]
    fn rebinding() {
        let ast = Parser::new(Lexer::new("let x = true; let x = 1; x + 1;"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRetConverter::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!("rebinding-xml", XmlWriter::new(&ast).serialize());
    }

    macro_rules! test_type_error {
        ($name:ident, $src:expr, $error:expr, $span:expr) => {
            #[test]
            fn $name() {
                let actual_diagnostics = Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRetConverter::new())
                    .resolve(Resolver::new(), Natives::default())
                    .unwrap_err();

                let actual_diagnostics_str = actual_diagnostics
                    .iter()
                    .map(|d| (d.message(), d.span().clone(), d.level()))
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
                Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRetConverter::new())
                    .resolve(Resolver::new(), Natives::new())
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
        "Expected type boolean, got number",
        Span::new(1, 4, 3, 2)
    );
    test_type_ok!(if_expected_boolean_condition_got_boolean, "if true {}");
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_binary,
        "if 40 + 2 {}",
        "Expected type boolean, got number",
        Span::new(1, 4, 3, 6)
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_expr_unary,
        "if - 42 {}",
        "Expected type boolean, got number",
        Span::new(1, 4, 3, 4)
    );
    test_type_error!(
        if_expected_boolean_condition_got_no_type,
        "if if true { ret 42; } else { ret 43; } {}",
        "Expected type boolean, got no type",
        Span::new(1, 4, 3, 36)
    );
    test_type_ok!(
        if_expected_boolean_condition_got_boolean_expr,
        "if 42 > 40 {}"
    );
    test_type_error!(
        if_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; if forty_two {}",
        "Expected type boolean, got number",
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
    test_type_ok!(if_no_false_branch, "if true { 42; }");
    test_type_ok!(if_type, "let n = 0 + if true { 42; } else { 0; };");
    test_type_error!(
        if_expected_boolean_condition_got_number_in_else_if,
        "if true {} else if 42 {}",
        "Expected type boolean, got number",
        Span::new(1, 20, 19, 2)
    );
    test_type_ok!(if_type_of_else_if, "if true { 42; } else if false { 0; }");
    test_type_error!(
        while_expected_boolean_condition_got_number,
        "while 42 {}",
        "Expected type boolean, got number",
        Span::new(1, 7, 6, 2)
    );
    test_type_error!(
        while_expected_boolean_condition_got_no_type,
        "while if true { ret 42; } else { ret 43; } {}",
        "Expected type boolean, got no type",
        Span::new(1, 7, 6, 36)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean,
        "while true {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_binary,
        "while 40 + 2 {}",
        "Expected type boolean, got number",
        Span::new(1, 7, 6, 6)
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_expr_unary,
        "while - 42 {}",
        "Expected type boolean, got number",
        Span::new(1, 7, 6, 4)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_expr,
        "while 42 > 40 {}"
    );
    test_type_error!(
        while_expected_boolean_condition_got_number_identifier,
        "let forty_two = 42; while forty_two {}",
        "Expected type boolean, got number",
        Span::new(1, 27, 26, 9)
    );
    test_type_ok!(
        while_expected_boolean_condition_got_boolean_identifier,
        "let t = true; while t {}"
    );
    test_type_error!(
        assignment_wrong_type,
        "let forty_two = 42; forty_two = true;",
        "Expected type number, got boolean",
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
        "Expected type number, got boolean",
        Span::new(1, 34, 33, 4)
    );
    test_type_error!(
        assignment_wrong_type_from_function,
        "let forty_two = 42; let f(): boolean = true; forty_two = f();",
        "Expected type number, got boolean",
        Span::new(1, 58, 57, 3)
    );
    test_type_error!(
        assignment_wrong_type_from_void_function,
        "let forty_two = 42; let f() = {} forty_two = f();",
        "Expected type number, got void",
        Span::new(1, 46, 45, 3)
    );
    test_type_error!(
        assignment_always_returning_expr,
        "let forty_two = 42; forty_two = if true { ret 42; } else { ret 43; };",
        "Expected type number, got no type",
        Span::new(1, 33, 32, 36)
    );
    test_type_ok!(
        assignment_correct_type_from_function,
        "let forty_two = 0; let f(): number = 42; forty_two = f();"
    );
    test_type_ok!(function_is_allowed_to_return_void, "let f() = { 1; }");
    test_type_ok!(function_has_struct_params, "struct S {} let f(s: S) = { }");
    // todo uncomment test_type_ok!(function_returns_struct, "struct S {} let f(): S = { }");
    test_type_error!(
        function_returns_void_but_expect_struct,
        "struct S {} let f(): S = { }",
        "Expected type struct, got void",
        Span::new(1, 13, 12, 16)
    );
    test_type_error!(
        function_void_cannot_return_number,
        "let f() = { ret 1; }",
        "Expected type void, got number",
        Span::new(1, 17, 16, 1)
    );
    test_type_error!(
        function_invalid_return_type,
        "let f(): unknown = { }",
        "'unknown' is not a known type",
        Span::new(1, 10, 9, 7)
    );
    test_type_error!(
        function_wrong_return_type,
        "let f(): boolean = { true; 42; }",
        "Expected type boolean, got number",
        Span::new(1, 28, 27, 2)
    );
    test_type_error!(
        function_wrong_return_type_2,
        "let f(): boolean = { }",
        "Expected type boolean, got void",
        Span::new(1, 1, 0, 22)
    );
    test_type_error!(
        function_wrong_early_return_type,
        "let f(): number = { if false { ret false; } 42; }",
        "Expected type number, got boolean",
        Span::new(1, 36, 35, 5)
    );
    test_type_ok!(
        function_parameter_returned_correct_type,
        "let f(n: number): number = { n; }"
    );
    test_type_error!(
        function_parameter_returned_wrong_type,
        "let f(n: number): boolean = { n; }",
        "Expected type boolean, got number",
        Span::new(1, 31, 30, 1)
    );
    // todo uncomment
    // test_type_error!(
    //     function_parameter_invalid_type,
    //     "let f(n: unknown) = { let a = n + true; }",
    //     "'unknown' in not a known type",
    //     Span::new(1, 32, 31, 1)
    // );
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
    test_type_ok!(
        fibonacci_rec,
        "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); }"
    );
    // fixme un-comment the following test
    // test_type_ok!(
    //     assign_from_native,
    //     "let n = add;"
    // );
}
