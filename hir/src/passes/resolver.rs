use crate::bound::{Bound, Unbound};
use crate::expression::{ExpressionKind, Target};
use crate::identifier::Identifier;
use crate::literal::LiteralKind;
use crate::natives::{Native, Natives, Type};
use crate::passes::exit_points_resolver::ExitPoint;
use crate::statement::{
    Annotation, Field, Implementation, Parameter, RetMode, Return, Statement, StatementKind,
    TypeDefKind,
};
use crate::symbol::{Symbol, SymbolKind};
use crate::typed::{Typed, Untyped};
use crate::{
    ResolvedExpression, ResolvedHir, ResolvedIdentifierRef, ResolvedStatement, UnresolvedHir,
};
use bimap::BiHashMap;
use std::collections::HashMap;
use std::mem;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;

type Function<T, B> = (
    Identifier<B>,
    Vec<Parameter<T, B>>,
    Return<T>,
    Implementation<ExprId>,
);

// todo:refactoring this would deserve a reordering of functions, and that each `resolve_` method
//   does the actual resolution instead of giving to its caller the information required to resolve

pub struct Resolver {
    // out
    identifiers: BiHashMap<IdentId, String>,
    identifier_refs: VecMap<IdentRefId, ResolvedIdentifierRef>,
    expressions: VecMap<ExprId, ResolvedExpression>,
    statements: VecMap<StmtId, ResolvedStatement>,
    types: BiHashMap<TypeId, Type>,
    types_by_name: HashMap<&'static str, TypeId>,
    symbols: VecMap<SymbolId, Symbol>,
    not_found_symbol_id: SymbolId,

    // work
    scope_stack: Vec<Scope>,
    /// maps functions (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    function_symbols: HashMap<StmtId, SymbolId>,
    /// maps structs (by their `StmtId`) to the corresponding symbol (by their `SymbolId`)
    struct_symbols: HashMap<StmtId, SymbolId>,
    annotation_symbols: HashMap<StmtId, SymbolId>,
    stmt_symbols: HashMap<(StmtId, usize), SymbolId>,

    diagnostics: Diagnostics,
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

            scope_stack: Default::default(),
            function_symbols: Default::default(),
            struct_symbols: Default::default(),
            annotation_symbols: Default::default(),
            stmt_symbols: Default::default(),

            diagnostics: Default::default(),
        }
    }

    pub fn resolve(
        mut self,
        natives: Natives,
        mut hir: UnresolvedHir,
    ) -> Result<ResolvedHir, Diagnostics> {
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

        // init. identifier_refs
        self.identifier_refs.resize(hir.identifier_refs.len());

        // init. expressions
        self.expressions.resize(hir.expressions.len());

        // init. statements
        self.statements.resize(hir.statements.len());

        // init. types
        debug_assert!(hir.types.is_empty());
        let invalid_type_id = TypeId::from(self.types.len());
        self.types.insert(invalid_type_id, Type::Invalid);

        let void_type_id = TypeId::from(self.types.len());
        self.types.insert(void_type_id, Type::Void);

        let none_type_id = TypeId::from(self.types.len());
        self.types.insert(none_type_id, Type::None);

        let boolean_type_id = TypeId::from(self.types.len());
        self.types.insert(boolean_type_id, Type::Boolean);

        let number_type_id = TypeId::from(self.types.len());
        self.types.insert(number_type_id, Type::Number);

        // init. symbols
        debug_assert!(hir.symbols.is_empty());
        let not_found_symbol_id = self.symbols.next_index();
        self.symbols.push(Symbol {
            id: not_found_symbol_id,
            kind: SymbolKind::NotFound,
            type_id: self.find_type_id_by_type(&Type::Invalid),
        });

        // init. scope_stack
        self.push_scope();

        let ident_ref_count = hir.identifier_refs.len();
        let expr_count = hir.expressions.len();
        let stmt_count = hir.statements.len();

        for native in natives.into_iter() {
            match native {
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

                    self.insert_symbol(
                        ident,
                        SymbolKind::Native(ident, parameters, ret_type, native.kind),
                        fn_type_id,
                    );
                }
                Native::Type(native) => {
                    let id = self.find_ident_id_by_str(native.name);
                    self.insert_symbol(
                        id,
                        SymbolKind::NativeType(id, native.ty.clone()),
                        self.find_type_id_by_type(&Type::None),
                    );
                }
            }
        }

        let root = hir.roots.clone();
        self.insert_annotations(&mut hir, &root);
        self.insert_structs(&mut hir, &root);
        self.insert_functions(&mut hir, &root);

        self.resolve_statements(&mut hir, &root);

        if !self.diagnostics.is_empty() {
            return Err(self.diagnostics);
        }

        let result = ResolvedHir {
            identifiers: VecMap::from_iter(self.identifiers),
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
            statements: self.statements,
            type_defs: hir.type_defs,
            roots: hir.roots,
            symbols: self.symbols,
            types: VecMap::from_iter(self.types),
            exit_points: hir.exit_points,
        };

        debug_assert!(
            !result.identifier_refs.has_holes(),
            "identifier_refs has holes. missing: {:?}; identifiers: {:?}",
            hir.identifier_refs,
            result.identifiers
        );
        debug_assert!(
            !result.expressions.has_holes(),
            "expressions has holes. missing: {:?}",
            hir.expressions
        );
        debug_assert!(
            !result.statements.has_holes(),
            "statements has holes. missing: {:?}",
            hir.statements
        );
        debug_assert!(
            !result.symbols.has_holes(),
            "symbols has holes. missing: {:?}",
            hir.symbols
        );
        debug_assert!(
            !result.types.has_holes(),
            "types has holes. missing: {:?}",
            hir.types
        );
        debug_assert!(
            hir.identifier_refs.is_empty(),
            "identifier_refs is not empty"
        );
        debug_assert!(
            ident_ref_count <= result.identifier_refs.len(),
            "ident_ref count does not match"
        );
        debug_assert!(hir.expressions.is_empty(), "expressions is not empty");
        debug_assert!(hir.statements.is_empty(), "statements is not empty");
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

    fn resolve_expression(&mut self, hir: &mut UnresolvedHir, expr_id: ExprId) -> TypeId {
        if let Some(expr) = self.expressions.get(expr_id) {
            return expr.resolved_type_id();
        }

        let expr = hir
            .expressions
            .remove(expr_id)
            .expect("expr is not resolved");

        let type_id = match &expr.kind {
            ExpressionKind::Assignment(Target::Direct(ident_ref), expr) => {
                self.resolve_assignment(hir, *ident_ref, *expr)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                let lhs_type_id = self.resolve_expression(hir, *lhs_expr_id);
                let rhs_type_id = self.resolve_expression(hir, *rhs_expr_id);

                if lhs_type_id == self.find_type_id_by_type(&Type::Invalid)
                    || rhs_type_id == self.find_type_id_by_type(&Type::Invalid)
                {
                    self.find_type_id_by_type(&Type::Invalid)
                } else if lhs_type_id != rhs_type_id {
                    self.diagnostics.report_err(
                        format!(
                            "RSH expected to be of type {}, got {}",
                            self.find_type_by_type_id(lhs_type_id),
                            self.find_type_by_type_id(rhs_type_id)
                        ),
                        self.expressions[*rhs_expr_id].span.clone(),
                        (file!(), line!()),
                    );
                    self.find_type_id_by_type(&Type::Invalid)
                } else {
                    lhs_type_id
                }
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.resolve_if(hir, *cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => match literal.kind {
                LiteralKind::Boolean(_) => self.find_type_id_by_type(&Type::Boolean),
                LiteralKind::Number(_) => self.find_type_id_by_type(&Type::Number),
                LiteralKind::String(_) => self
                    .find_type_id_by_name("string")
                    .expect("string type exists"),
                LiteralKind::Identifier(ident_ref) => self
                    .resolve_ident_ref(hir, ident_ref, None)
                    .map(|s| self.symbols[s].type_id)
                    .unwrap_or(self.find_type_id_by_type(&Type::Invalid)),
            },
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                let ident_ref = hir
                    .identifier_refs
                    .remove(*ident_ref_id)
                    .expect("ident_ref exists");

                let expr_type_id = self.resolve_expression(hir, *expr_id);

                let ty = self.find_type_by_type_id(expr_type_id);
                let field_type_id = match ty {
                    Type::Struct(stmt_id) => match &self.statements[*stmt_id].kind {
                        StatementKind::Struct(ident, _, Implementation::Provided(fields)) => {
                            match fields
                                .iter()
                                .enumerate()
                                .find(|(_, field)| field.identifier.id == ident_ref.ident.id)
                            {
                                Some((index, field)) => {
                                    let field_symbol_id = self
                                        .find_symbol_id_for_struct_field(*stmt_id, index)
                                        .expect("field exists");
                                    let ident_ref = ident_ref.resolved(field_symbol_id);
                                    self.identifier_refs.insert(ident_ref.id, ident_ref);
                                    field.resolved_type_id()
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
                                    let ident_ref = ident_ref.resolved(self.not_found_symbol_id);
                                    self.identifier_refs.insert(ident_ref.id, ident_ref);
                                    self.find_type_id_by_type(&Type::Invalid)
                                }
                            }
                        }
                        StatementKind::Struct(ident, _, _) => {
                            self.diagnostics.report_err(
                                format!(
                                    "Native struct {} fields cannot be accessed",
                                    self.identifiers.get_by_left(&ident.id).unwrap()
                                ),
                                expr.span.clone(),
                                (file!(), line!()),
                            );
                            self.find_type_id_by_type(&Type::Invalid)
                        }
                        _ => panic!("struct expected"),
                    },
                    _ => {
                        self.diagnostics.report_err(
                            format!("Expected struct type, got {}", ty),
                            self.expressions[*expr_id].span.clone(),
                            (file!(), line!()),
                        );

                        // this it not always true (the left hand side can be a symbol), but it not
                        // being a struct field anyway, considering we did not find any symbol is
                        // (probably) fine...
                        let ident_ref = ident_ref.resolved(self.not_found_symbol_id);
                        self.identifier_refs.insert(ident_ref.id, ident_ref);
                        self.find_type_id_by_type(&Type::Invalid)
                    }
                };

                field_type_id
            }
            ExpressionKind::FunctionCall(expr_id, params) => {
                self.resolve_function_call(hir, *expr_id, params.clone().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.resolve_while(hir, *cond, *expr),
            ExpressionKind::Block(stmts) => self.resolve_block(hir, &stmts.clone()),
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                self.resolve_struct_instantiation(hir, *ident_ref_id, fields, &expr.span)
            }
            ExpressionKind::ArrayInstantiation(values) => {
                self.resolve_array_instantiation(hir, values)
            }
            ExpressionKind::ArrayAccess(expr, index) => {
                self.resolve_array_access(hir, *expr, *index)
            }
        };

        self.expressions.insert(expr_id, expr.typed(type_id));

        type_id
    }

    fn resolve_assignment(
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

        let rhs_type_id = self.resolve_expression(hir, expr);

        let lhs_type_id = self
            // todo:feature:fn-value to search for method, we need to extract the parameter types from the
            //  expr_type, if it corresponds to a function type. We don't have this
            //  information yet and thus we cannot assign to a variable holding a function
            //  (yet).
            .resolve_ident_ref(hir, ident_ref, None)
            .map(|s| self.symbols[s].type_id)
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
                    "RSH expected to be of type {}, got {}",
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

    fn resolve_if(
        &mut self,
        hir: &mut UnresolvedHir,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> TypeId {
        let cond_type = self.resolve_expression(hir, cond);

        if cond_type != self.find_type_id_by_type(&Type::Boolean)
            && cond_type != self.find_type_id_by_type(&Type::Invalid)
        {
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

        let true_branch_type_id = self.resolve_expression(hir, true_branch);
        let false_branch_type_id = match false_branch {
            None => self.find_type_id_by_type(&Type::Void),
            Some(e) => self.resolve_expression(hir, e),
        };

        let true_branch_type = self.find_type_by_type_id(true_branch_type_id);
        let false_branch_type = self.find_type_by_type_id(false_branch_type_id);

        match (true_branch_type, false_branch_type) {
            (Type::Invalid, _) | (_, Type::Invalid) => self.find_type_id_by_type(&Type::Invalid),
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
                self.find_type_id_by_type(&Type::Invalid)
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
            let param_type = self.resolve_expression(hir, *param);

            if param_type != invalid_type_id {
                param_types.push(param_type)
            }
        }

        if param_types.len() != params.len() {
            return self.find_type_id_by_type(&Type::Invalid);
        }

        // todo:refactor this is not amazing: we extract the identifier ref, then we resolve it,
        //  and finally we resolve the expression. this needs to be reworked when we add support
        //  for "anonymous functions"

        let expression = &hir.expressions[expr_id];
        let ident_ref_id = match &expression.kind {
            ExpressionKind::Literal(lit) => match lit.kind {
                LiteralKind::Identifier(ident_ref) => ident_ref,
                _ => panic!("Identifier(IdentRefId) expected, got {expression:?}"),
            },
            _ => panic!("Literal(Literal) expected, got {expression:?}"),
        };

        let type_id = self
            .resolve_ident_ref(hir, ident_ref_id, Some(&param_types))
            .map(|s| match &self.symbols[s].kind {
                SymbolKind::LetFn(_, _, _, ret_type) => *ret_type,
                SymbolKind::Native(_, _, ret_type, _) => *ret_type,
                SymbolKind::NotFound => self.find_type_id_by_type(&Type::Invalid),
                _ => {
                    // todo:ux better error (i.e. produce a diagnostic)
                    panic!("the resolved symbol was not a function")
                }
            })
            .unwrap_or(self.find_type_id_by_type(&Type::Invalid));

        self.resolve_expression(hir, expr_id);

        type_id
    }

    fn resolve_while(&mut self, hir: &mut UnresolvedHir, cond: ExprId, expr: ExprId) -> TypeId {
        let cond_type = self.resolve_expression(hir, cond);

        if cond_type != self.find_type_id_by_type(&Type::Boolean)
            && cond_type != self.find_type_id_by_type(&Type::Invalid)
        {
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
        self.push_scope();

        self.insert_functions(hir, stmts);
        let stmts_type_id = self.resolve_statements(hir, stmts);

        self.pop_scope();

        stmts_type_id
    }

    fn resolve_struct_instantiation(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref_id: IdentRefId,
        field_exprs: &[(IdentRefId, ExprId)],
        span: &Span,
    ) -> TypeId {
        let mut expr_type_ids = Vec::with_capacity(field_exprs.len());
        for (_, field_expr_id) in field_exprs {
            let expr_type_id = self.resolve_expression(hir, *field_expr_id);
            expr_type_ids.push(expr_type_id);
        }
        debug_assert!(expr_type_ids.len() == field_exprs.len());

        let struct_def = self
            .resolve_ident_ref(hir, ident_ref_id, None)
            .map(|sid| &self.symbols[sid])
            .and_then(|s| match s.kind {
                SymbolKind::Struct(_, stmt_id) => Some(&self.statements[stmt_id]),
                _ => None,
            })
            .map(|s| match &s.kind {
                StatementKind::Struct(struct_identifier, _, struct_fields) => {
                    (s.id, struct_identifier, struct_fields)
                }
                _ => panic!("must be a struct"),
            });

        if let Some((struct_stmt_id, struct_identifier, implementation)) = struct_def {
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

            for ((field_ident_ref_id, field_expr_id), expr_type_id) in
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

            self.find_type_id_by_identifier(struct_identifier.id)
                .expect("type exists")
        } else {
            self.find_type_id_by_type(&Type::Invalid)
        }
    }

    fn resolve_array_instantiation(
        &mut self,
        hir: &mut UnresolvedHir,
        values: &[ExprId],
    ) -> TypeId {
        let expected_type_id = self.resolve_expression(
            hir,
            *values.first().expect("array has at least one element"),
        );

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
            let type_id = self.resolve_expression(hir, *expr_id);
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
        let array_type_id = self.resolve_expression(hir, base_expr_id);
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

        let index_type_id = self.resolve_expression(hir, value_expr_id);
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

    // todo:refactoring think about passing the Statement directly
    fn resolve_statements(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) -> TypeId {
        let mut ret_type = self.find_type_id_by_type(&Type::Void);

        for &stmt_id in stmts {
            let stmt_type = if let Some(stmt) = hir.statements.remove(stmt_id) {
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

                self.resolve_expression(hir, expr)
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
            ) => {
                let res = self.resolve_function(
                    hir,
                    stmt_id,
                    (ident, params, ret_type, Implementation::Provided(expr)),
                    &annotations,
                    &span,
                );

                if let Ok((identifier, parameters, ret_type, implementation)) = res {
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
                            ),
                            span,
                        ),
                    );
                }

                self.find_type_id_by_type(&Type::Void)
            }
            #[cfg(debug_assertions)]
            StatementKind::LetFn(_, _, _, _, Implementation::Native(_)) => {
                panic!("body type must be implemented before resolution");
            }
            #[cfg(not(debug_assertions))]
            StatementKind::LetFn(_, _, _, _, Implementation::Native) => {
                panic!("body type must be implemented before resolution");
            }
            StatementKind::Struct(ident, annotations, implementation) => {
                let fields = match implementation {
                    Implementation::Provided(fields) => fields,
                    _ => panic!("implementation required"),
                };
                let (ident, fields) =
                    self.resolve_struct(hir, stmt_id, ident, fields, &annotations);

                self.statements.insert(
                    stmt_id,
                    Statement::new(
                        stmt_id,
                        StatementKind::Struct(ident, annotations, fields),
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
        }
    }

    fn resolve_let(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt: StmtId,
        ident: &Identifier<Unbound>,
        expr: ExprId,
    ) -> SymbolId {
        let expr_type_id = self.resolve_expression(hir, expr);

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
    ) -> Result<Function<Typed, Bound>, ()> {
        let body_expr_id = match implementation {
            Implementation::Provided(expr_id) => expr_id,
            _ => panic!("implementation required"),
        };
        self.push_scope();

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

        // todo:feature manage duplicate functions (for whatever it means ... - at least same name same
        //   first parameter type)

        let symbol_id = *self
            .function_symbols
            .get(&stmt_id)
            .expect("function was inserted");

        let (param_types, ret_type_id) = self.symbols[symbol_id].as_function();
        let param_types = param_types.clone();

        #[cfg(test)]
        println!(
            "Visiting function {name} ({symbol_id:?}) with return type {ret_type}",
            name = self.identifiers.get_by_left(&ident.id).unwrap(),
            ret_type = self.types.get_by_left(&ret_type_id).unwrap()
        );

        let mut success = ret_type_id != self.find_type_id_by_type(&Type::Invalid);

        let params_len = params.len();
        let parameters = params
            .into_iter()
            .zip(param_types)
            .enumerate()
            .filter_map(|(index, (parameter, type_id))| {
                let ident_id = parameter.identifier.id;
                let symbol_kind = SymbolKind::Parameter(ident_id, stmt_id, index);

                if self.symbol_exists_in_current_scope(ident_id, &symbol_kind) {
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

        success = success && parameters.len() == params_len;

        let is_native = self.native_annotation_present(hir, annotations);
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
                success = false;
            }
        }

        // we want to visit the expression, hence no short-circuit
        // note that we resolve the expression even for native function (even though we don't
        // report any error whatsoever so that we don't have "holes" in the resolved expressions)
        let expr_type_id = self.resolve_expression(hir, body_expr_id);

        if !is_native {
            success = expr_type_id != self.find_type_id_by_type(&Type::Invalid) && success;

            if ret_type_id != self.find_type_id_by_type(&Type::Invalid) {
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
                    panic!(
                        "we must always have at least one exit point, even if implicit and void"
                    );
                }

                #[cfg(test)]
                println!(
                    "Exit points of {name} ({body_expr_id:?}): {exit_points:?}",
                    name = self.identifiers.get_by_left(&ident.id).unwrap(),
                );

                for (exit_expr_id, explicit) in exit_points {
                    let expr_type_id = match exit_expr_id {
                        None => self.find_type_id_by_type(&Type::Void),
                        Some(exit_expr_id) => self.resolve_expression(hir, exit_expr_id),
                    };

                    if expr_type_id == self.find_type_id_by_type(&Type::Invalid) {
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
        }

        self.pop_scope();

        if success {
            let symbol_id = self.find_symbol_id_by_ident_and_param_types(
                ident.id,
                Some(
                    &parameters
                        .iter()
                        .map(|p| p.resolved_type_id())
                        .collect::<Vec<TypeId>>(),
                ),
            );

            if let Some(symbol_id) = symbol_id {
                return Ok((
                    ident.bind(symbol_id),
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
                ));
            }
        }

        Err(())
    }

    fn resolve_struct(
        &mut self,
        hir: &mut UnresolvedHir,
        stmt_id: StmtId,
        identifier: Identifier<Unbound>,
        fields: Vec<Field<Untyped, Unbound>>,
        annotations: &[Annotation],
    ) -> (Identifier<Bound>, Implementation<Vec<Field<Typed, Bound>>>) {
        let is_native = self.native_annotation_present(hir, annotations);
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
        self.push_scope();

        let fields = fields
            .into_iter()
            .enumerate()
            .map(|(index, field)| {
                let ident_id = field.identifier.id;
                let symbol_kind = SymbolKind::Field(ident_id, stmt_id, index);

                if self.symbol_exists_in_current_scope(ident_id, &symbol_kind) {
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

        self.pop_scope();

        let symbol_id = self
            .struct_symbols
            .get(&stmt_id)
            .cloned()
            // todo:refactoring same handling as for visit_function: if not found, return Err()
            //   or, return not_found_symbol_id in visit_function. This requires that the find_*()
            //   and resolve_*() function are reworked...
            // it may happen that the struct is not found in case of duplicate def.
            .unwrap_or(self.not_found_symbol_id);

        (
            identifier.bind(symbol_id),
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
            // todo:refactoring same handling as for visit_function: if not found, return Err()
            //   or, return not_found_symbol_id in visit_function. This requires that the find_*()
            //   and resolve_*() function are reworked...
            // it may happen that the annotation is not found in case of duplicate def.
            .unwrap_or(self.not_found_symbol_id);

        identifier.bind(symbol_id)
    }

    /// Resolves an identifier ref by its `IdentRefId` and returns the corresponding `SymbolId`.
    /// The resolution starts in the current scope and crawls the scopes stack up until the
    /// identifier is found.
    fn resolve_ident_ref(
        &mut self,
        hir: &mut UnresolvedHir,
        ident_ref_id: IdentRefId,
        param_types: Option<&[TypeId]>,
    ) -> Option<SymbolId> {
        if let Some(ident_ref) = &self.identifier_refs.get(ident_ref_id) {
            return Some(ident_ref.resolved_symbol_id());
        }

        let ident_ref = hir
            .identifier_refs
            .remove(ident_ref_id)
            .expect("ident_ref is not resolved");

        let ident_id = ident_ref.ident.id;
        match self.find_symbol_id_by_ident_and_param_types(ident_id, param_types) {
            Some(s) => {
                self.identifier_refs
                    .insert(ident_ref.id, ident_ref.resolved(s));
                Some(s)
            }
            None => {
                // todo:feature propose known alternatives
                if let Some(param_types) = param_types {
                    // todo:refactoring move that to caller side
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
                } else {
                    // todo:refactoring move that to caller side
                    self.diagnostics.report_err(
                        format!(
                            "Identifier '{}' not found",
                            self.identifiers.get_by_left(&ident_id).unwrap()
                        ),
                        ident_ref.ident.span.clone(),
                        (file!(), line!()),
                    );
                }

                // still, resolve it to an unknown symbol
                self.identifier_refs
                    .insert(ident_ref.id, ident_ref.resolved(self.not_found_symbol_id));

                None
            }
        }
    }

    fn resolve_type_def(&mut self, hir: &mut UnresolvedHir, type_def_id: TypeDefId) {
        match hir.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_id) => {
                self.resolve_ident_ref(hir, ident_ref_id, None);
            }
            TypeDefKind::Array(type_def_id, _) => {
                self.resolve_type_def(hir, type_def_id);
            }
        }
    }

    fn native_annotation_present(
        &mut self,
        hir: &mut UnresolvedHir,
        annotations: &[Annotation],
    ) -> bool {
        for annotation in annotations.iter() {
            // note that the diagnostic in case the identifier is not found is generated in
            // `resolve_ident_ref`. There is a comment inside of it that says to move the diagnostic
            // generation on the caller side.
            if let Some(symbol_id) = self.resolve_ident_ref(hir, annotation.ident_ref_id, None) {
                let annotation_ident_id = self.symbols[symbol_id].as_annotation();

                if self.identifiers.get_by_left(annotation_ident_id).unwrap() == "native" {
                    return true;
                }
            }
        }
        false
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
            .find_map(|scope| scope.find(&self.symbols, &ident, param_types))
    }

    fn find_symbol_id_for_struct_field(&self, stmt_id: StmtId, index: usize) -> Option<SymbolId> {
        self.stmt_symbols
            .get(&(stmt_id, index))
            .and_then(|sid| self.symbols.get(*sid))
            .and_then(|s| match s.kind {
                SymbolKind::Field(_, _, _) => Some(s.id),
                _ => None,
            })
    }

    fn insert_functions(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) {
        // first, we resolve all the identifier refs for parameter types and return type ...
        let ident_ref_ids = stmts
            .iter()
            .filter_map(|stmt_id| match &hir.statements[*stmt_id].kind {
                StatementKind::LetFn(_, _, params, ret, ..) => {
                    let mut type_def_ids = params
                        .iter()
                        .map(|p| p.type_def_id)
                        .collect::<Vec<TypeDefId>>();

                    if let Some(type_def) = &ret.type_def_id {
                        type_def_ids.push(*type_def);
                    }

                    Some(type_def_ids)
                }
                _ => None,
            })
            .flatten()
            .collect::<Vec<TypeDefId>>();

        for ident_ref_id in ident_ref_ids.into_iter() {
            self.resolve_type_def(hir, ident_ref_id);
        }

        // ... then, we proceed with the function
        let functions = stmts
            .iter()
            .filter_map(|stmt_id| match &hir.statements[*stmt_id].kind {
                StatementKind::LetFn(ident, _, params, ret_type, expr_id) => {
                    let parameter_types = params
                        .iter()
                        .map(|p| {
                            self.find_type_id_by_type_def_id(hir, p.type_def_id)
                                .unwrap_or(self.find_type_id_by_type(&Type::Invalid))
                        })
                        .collect::<Vec<TypeId>>();

                    let ret_type_id = ret_type
                        .type_def_id
                        .as_ref()
                        .map(|type_def_id| {
                            self.find_type_id_by_type_def_id(hir, *type_def_id)
                                .unwrap_or(self.find_type_id_by_type(&Type::Invalid))
                        })
                        .unwrap_or(self.find_type_id_by_type(&Type::Void));

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
            .collect::<Vec<(
                Identifier<Unbound>,
                StmtId,
                Vec<TypeId>,
                TypeId,
                Implementation<ExprId>,
            )>>();

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

    /// Inserts all structs found in `stmts` into `self.struct_symbols` (which itself contains
    /// reference to `self.symbols`) as well as the current stack frame's symbol table. While doing
    /// so, we perform the following:
    ///  - insert a type corresponding to the struct in `self.types`;
    ///  - verify that no struct with the same name already exist in the current scope;
    ///  - resolve the fields' types.
    fn insert_structs(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) {
        // we start by inserting all the structs we find, so that the types are available from
        // everywhere in the current scope.

        // first, we collect and insert all structs
        let structs = stmts
            .iter()
            .filter_map(|stmt| match &hir.statements[*stmt].kind {
                StatementKind::Struct(ident, _, _) => Some((*stmt, ident.clone())),
                _ => None,
            })
            .collect::<Vec<(StmtId, Identifier<Unbound>)>>();

        for (stmt_id, identifier) in structs.into_iter() {
            let ident_id = identifier.id;
            let symbol_kind = SymbolKind::Struct(ident_id, stmt_id);

            if self.symbol_exists_in_current_scope(ident_id, &symbol_kind) {
                self.diagnostics.report_err(
                    format!(
                        "Struct '{ident}' is already defined in scope",
                        ident = self.identifiers.get_by_left(&ident_id).unwrap(),
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
        let type_def_ids = stmts
            .iter()
            .filter_map(|stmt_id| match &hir.statements[*stmt_id].kind {
                StatementKind::Struct(_, _, Implementation::Provided(fields)) => Some(
                    fields
                        .iter()
                        .map(|p| p.type_def_id)
                        .collect::<Vec<TypeDefId>>(),
                ),
                StatementKind::Struct(_, _, _) => panic!("implementation required"),
                _ => None,
            })
            .flatten()
            .collect::<Vec<TypeDefId>>();

        for type_def_id in type_def_ids.into_iter() {
            self.resolve_type_def(hir, type_def_id);
        }
    }

    fn insert_annotations(&mut self, hir: &mut UnresolvedHir, stmts: &[StmtId]) {
        let annotations = stmts
            .iter()
            .filter_map(|stmt| match &hir.statements[*stmt].kind {
                StatementKind::Annotation(ident) => Some((*stmt, ident.clone())),
                _ => None,
            })
            .collect::<Vec<(StmtId, Identifier<Unbound>)>>();

        for (stmt_id, identifier) in annotations.into_iter() {
            let ident_id = identifier.id;
            let symbol_kind = SymbolKind::Annotation(ident_id, stmt_id);

            if self.symbol_exists_in_current_scope(ident_id, &symbol_kind) {
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
                self.annotation_symbols.insert(stmt_id, symbol_id);
            }
        }
    }

    /// Returns `true` if a symbol of the same kind already exists in the current scope.
    fn symbol_exists_in_current_scope(&self, ident_id: IdentId, kind: &SymbolKind) -> bool {
        match self
            .scope_stack
            .last()
            .expect("current scope exists")
            .symbols
            .get(&ident_id)
        {
            None => false,
            Some(symbols) => symbols.iter().map(|s| &self.symbols[*s]).any(|s| {
                matches!(
                    (&s.kind, kind),
                    (SymbolKind::Parameter(..), SymbolKind::Parameter(..))
                        | (SymbolKind::Field(..), SymbolKind::Field(..))
                        | (SymbolKind::Struct(..), SymbolKind::Struct(..))
                        | (SymbolKind::Annotation(..), SymbolKind::Annotation(..))
                )
            }),
        }
    }

    fn insert_symbol(&mut self, ident_id: IdentId, kind: SymbolKind, ty: TypeId) -> SymbolId {
        let symbol_id = self.symbols.create();

        match &kind {
            SymbolKind::Parameter(_, stmt_id, index) | SymbolKind::Field(_, stmt_id, index) => {
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
        *self.identifiers.get_by_right(name).unwrap()
    }

    /// Inserts a `Type` if it does not already exist and returns its `TypeId`. If the type already
    /// exists, returns it's `TypeId`
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

    fn find_type_id_by_type_def_id(
        &mut self,
        hir: &UnresolvedHir,
        type_def_id: TypeDefId,
    ) -> Option<TypeId> {
        match &hir.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_id) => {
                self.find_type_id_by_identifier(self.identifier_refs[*ident_ref_id].ident.id)
            }
            TypeDefKind::Array(type_def_id, len) => self
                .find_type_id_by_type_def_id(hir, *type_def_id)
                .map(|base| Type::Array(base, *len))
                .map(|t| self.insert_type(t)),
        }
    }

    fn find_type_id_by_identifier(&self, ident_id: IdentId) -> Option<TypeId> {
        self.find_symbol_id_by_ident_and_param_types(ident_id, None)
            .and_then(|symbol_id| match &self.symbols[symbol_id].kind {
                SymbolKind::NativeType(_, ty) => Some(self.find_type_id_by_type(ty)),
                SymbolKind::Struct(_, stmt) => {
                    Some(self.find_type_id_by_type(&Type::Struct(*stmt)))
                }
                _ => None,
            })
    }

    fn find_type_id_by_name(&mut self, name: &'static str) -> Option<TypeId> {
        if let Some(type_id) = self.types_by_name.get(name) {
            return Some(*type_id);
        }
        let type_id = self
            .identifiers
            .get_by_right(name)
            .and_then(|ident_id| self.find_type_id_by_identifier(*ident_id));
        if let Some(type_id) = type_id {
            self.types_by_name.insert(name, type_id);
        }
        type_id
    }

    fn find_type_id_by_type(&self, ty: &Type) -> TypeId {
        *self.types.get_by_right(ty).unwrap()
    }

    fn find_type_by_type_id(&self, ty: TypeId) -> &Type {
        self.types
            .get_by_left(&ty)
            .unwrap_or_else(|| panic!("type {ty} exists"))
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::new());
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
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

    /// Find among `all_symbols` one that is in the current scope and that matches the `param_types`
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
                            | SymbolKind::Annotation(_, _)
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
                            | SymbolKind::Struct(_, _)
                            | SymbolKind::Annotation(_, _) => false,
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
    use crate::UnresolvedHir;
    use insta::assert_debug_snapshot;
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

        assert_debug_snapshot!(hir);
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

        assert_debug_snapshot!(hir);
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

        assert_debug_snapshot!(hir);
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

        assert_debug_snapshot!(hir);
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

        assert_debug_snapshot!(hir);
    }

    #[test]
    fn fibonacci_rec() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new(
                r#"
            let main(n: number): number {
                if n < 2 {
                    ret n;
                }
                main(n - 1) + main(n - 2);
            }
            "#,
            ))
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

    #[test]
    fn annotation_function_bindings() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("annotation a; @a let f() {}"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::empty())
        .unwrap();
        assert_debug_snapshot!(&hir);
    }
    #[test]
    fn annotation_native_function_bindings() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("annotation native; @native let f() {}"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::empty())
        .unwrap();
        assert_debug_snapshot!(&hir);
    }
    #[test]
    fn annotation_struct_bindings() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("annotation a; @a struct S {}"))
                .parse()
                .unwrap(),
        )
        .resolve(Natives::empty())
        .unwrap();
        assert_debug_snapshot!(&hir);
    }
    #[test]
    fn annotation_native_struct_bindings() {
        let hir = UnresolvedHir::from(
            Parser::new(Lexer::new("annotation native; @native struct S {}"))
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
        Span::new(1, 26, 25, 3)
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
        Span::new(1, 20, 19, 3)
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
    test_type_ok!(
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
    test_type_ok!(
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
    test_type_ok!(nested_function_same_type, "let f() { let g() {} }");
    test_type_ok!(
        nested_function_different_types,
        "let f(): number { let g(): boolean { true; }; 1; }"
    );

    test_type_ok!(
        struct_same_field_name,
        r#"
        struct Inner { field: number };
        struct Outer { field: number };
        "#
    );
    test_type_ok!(
        struct_instantiation_same_field_name,
        r#"
        struct Inner { field: number };
        struct Outer { field: Inner };
        let s = Outer { field: Inner { field: 1 } };
        "#
    );

    test_type_ok!(void_function_explicit_void_ret, "let f() { ret; }");
    test_type_ok!(void_function_implicit_void_ret, "let f() { }");
    test_type_ok!(void_function_implicit_number_ret, "let f() { 1; }");
    test_type_error!(
        non_void_function_explicit_void_ret,
        r#"let f(): number { ret; }"#,
        "Function f expected to return type number, got void",
        Span::new(1, 17, 16, 8)
    );
    test_type_error!(
        non_void_function_implicit_void_ret,
        "let f(): number { }",
        "Function f expected to return type number, got void",
        Span::new(1, 17, 16, 3)
    );

    test_type_error!(
        let_from_void,
        "let g() {} let f() { let a = g(); }",
        "Expected some type, got void",
        Span::new(1, 30, 29, 3)
    );

    test_type_error!(
        return_from_void,
        "let g() {} let f(): number { g(); }",
        "Function f expected to return type number, got void",
        Span::new(1, 30, 29, 3)
    );

    test_type_ok!(
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
    test_type_ok!(
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
    test_type_error!(
        struct_assignment_wrong_type,
        r#"
        struct S {
            field: number
        }
        let f() {
            let s = S { field: 1 };
            s.field = false;
        }
        "#,
        "RSH expected to be of type number, got boolean",
        Span::new(7, 23, 132, 5)
    );

    test_type_ok!(
        array_homogenous_types,
        r#"
        let f() {
            let a = [0, 1];
        }
        "#
    );
    test_type_ok!(
        array_return_type,
        r#"
        let f(): [number; 2] {
            [0, 1];
        }
        "#
    );
    test_type_error!(
        array_return_type_wrong_len,
        r#"
        let f(): [number; 2] {
            [0, 1, 2];
        }
        "#,
        "Function f expected to return type array[2], got array[3]",
        Span::new(3, 13, 44, 9)
    );
    test_type_error!(
        array_return_type_wrong_base_typee,
        r#"
        let f(): [number; 2] {
            [true, false];
        }
        "#,
        "Function f expected to return type array[2], got array[2]",
        Span::new(3, 13, 44, 13)
    );
    test_type_ok!(
        array_parameter_type,
        r#"
        let f(a: [number; 2]) {
        }
        let g() {
            f([1, 2]);
        }
        "#
    );
    test_type_ok!(
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
    test_type_ok!(
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
    test_type_error!(
        array_heterogeneous_types,
        "let f() { let a = [0, false]; }",
        "Expected value of type number, got boolean at index 1",
        Span::new(1, 23, 22, 5)
    );
    test_type_error!(
        array_type_1,
        "let f() { if true { [0, 1]; } else { [2, 3, 4]; } }",
        "Expected type array[2], got array[3]",
        Span::new(1, 36, 35, 14)
    );
    // todo:ux we must have the inner type name in the error (this has to do with the Display impl.
    //   of Type
    test_type_error!(
        array_type_2,
        "let f() { if true { [0, 1]; } else { [true, false]; } }",
        "Expected type array[2], got array[2]",
        Span::new(1, 36, 35, 18)
    );
    test_type_ok!(array_access, "let f() { let a = [0]; a[0]; }");
    test_type_ok!(array_write_access, "let f() { let a = [0]; a[0] = 1; }");
    test_type_error!(
        array_write_access_wrong_type,
        "let f() { let a = [0]; a[0] = false; }",
        "RSH expected to be of type number, got boolean",
        Span::new(1, 31, 30, 5)
    );
    test_type_ok!(array_instantiation_and_access, "let f() { [0, 1][0]; }");
    test_type_error!(
        array_access_not_array,
        "let f() { let a = 1; a[0]; }",
        "Expected type array, got number",
        Span::new(1, 22, 21, 1)
    );
    test_type_error!(
        array_access_not_numeric_index,
        "let f() { let a = [0]; a[true]; }",
        "Expected index to be of type number, got boolean",
        Span::new(1, 24, 23, 1)
    );
    test_type_error!(
        array_return_wrong_length,
        "let f(): [number; 1] { [0, 1]; }",
        "Function f expected to return type array[1], got array[2]",
        Span::new(1, 24, 23, 6)
    );
    test_type_error!(
        array_parameter_wrong_length,
        r#"
        let f(a: [number; 2]) {
        }
        let g() {
            f([1, 2, 3]);
        }
        "#,
        "No function 'f' found for parameters of types (array[3])",
        Span::new(5, 13, 73, 1)
    );
    test_type_ok!(define_annotation, "annotation a;");
    test_type_ok!(
        native_function_have_no_body,
        r#"
        annotation native;
        @native let f(): number { }
        "#
    );
    test_type_error!(
        native_function_must_not_have_body,
        r#"
        annotation native;
        @native let f(): number { true; }
        "#,
        "Native function f must not have a body",
        Span::new(3, 33, 60, 9)
    );
    test_type_ok!(
        non_native_function_have_body,
        r#"
        annotation non_native;
        @non_native let f(): number { 10; }
        "#
    );
    test_type_ok!(
        native_struct_have_no_body,
        r#"
        annotation native;
        @native struct S {}
        "#
    );
    test_type_error!(
        native_struct_must_not_have_body,
        r#"
        annotation native;
        @native struct S { field1: number, field2: number }
        "#,
        "Native struct S must not have a body",
        Span::new(3, 28, 55, 30)
    );
    test_type_error!(
        native_struct_cannot_be_instantiated,
        r#"
        annotation native;
        @native struct S {  }
        let f() {
            let s = S {};
        }
        "#,
        "Native struct S cannot be instantiated",
        Span::new(5, 21, 96, 4)
    );
    test_type_error!(
        native_struct_fields_cannot_be_accessed,
        r#"
        annotation native;
        @native struct S {  }
        let f(s: S) {
            s.whatever;
        }
        "#,
        "Native struct S fields cannot be accessed",
        Span::new(5, 13, 92, 10)
    );
    test_type_ok!(
        non_native_struct_have_body,
        r#"
        annotation non_native;
        @non_native struct S { field: number }
        "#
    );
    test_type_error!(
        unknown_function_annotation,
        r#"
        @unknown let f(): number { 10; }
        "#,
        "Identifier 'unknown' not found",
        Span::new(2, 10, 10, 7)
    );
    test_type_error!(
        unknown_struct_annotation,
        r#"
        @unknown struct S {}
        "#,
        "Identifier 'unknown' not found",
        Span::new(2, 10, 10, 7)
    );
    test_type_error!(
        void_in_arrays,
        r#"
        let main() { let a = [ f() ]; }
        let f() {}
        "#,
        "Void values cannot be used as array elements at index 0",
        Span::new(1, 32, 32, 3)
    );
    test_type_ok!(
        native_struct_can_be_used,
        r#"
        annotation native;
        @native struct string {}
        @native let print(s: string) {}
        let main() {
            let hello = "hello";
            print(hello);
        }
        "#
    );
}
