use std::collections::BTreeMap;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{
    ExprId, FunctionId, IdentId, IdentRefId, NamespaceId, StmtId, StructId, SymbolId, TypeId,
};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;
use transmute_hir::expression::{ExpressionKind as HirExpressionKind, Target as HirTarget};
use transmute_hir::literal::{Literal as HirLiteral, LiteralKind as HirLiteralKind};
use transmute_hir::natives::Type as HirType;
use transmute_hir::statement::{RetMode, StatementKind as HirStatementKind};
use transmute_hir::symbol::SymbolKind as HirSymbolKind;
use transmute_hir::{
    ResolvedExpression as HirExpression, ResolvedField as HirField,
    ResolvedIdentifier as HirIdentifier, ResolvedIdentifierRef as HirIdentifierRef,
    ResolvedParameter as HirParameter,
};
use transmute_hir::{ResolvedHir as Hir, ResolvedReturn as HirReturn};
// todo:refactoring move to MIR?
pub use transmute_hir::natives::NativeFnKind;
// todo:refactoring copy to MIR?
pub use transmute_hir::statement::Implementation;

// todo:refactor:style get rid of the `#[allow(clippy::too_many_arguments)]`

pub fn make_mir(hir: Hir) -> Result<Mir, Diagnostics<()>> {
    Mir::try_from(hir)
}

// todo:refactoring should not be `VecMap`s, they are sparse
struct Transformer {
    functions: VecMap<FunctionId, Function>,
    structs: VecMap<StructId, Struct>,
    // todo:refactoring only keep one of SymbolId or StructId?
    structs_map: VecMap<StmtId, (SymbolId, StructId)>,
    fn_map: VecMap<StmtId, FunctionId>,
    expressions: VecMap<ExprId, Expression>,
    statements: VecMap<StmtId, Statement>,
    /// Maps a `NamespaceId` to it's parent's `NamespaceId` (if it has one) and it's `IdentId`
    namespaces: VecMap<NamespaceId, (Option<NamespaceId>, IdentId)>,
}

impl Transformer {
    pub fn new() -> Self {
        Self {
            functions: Default::default(),
            structs: Default::default(),
            structs_map: Default::default(),
            fn_map: Default::default(),
            expressions: Default::default(),
            statements: Default::default(),
            namespaces: Default::default(),
        }
    }

    pub fn transform(mut self, mut hir: Hir) -> Result<Mir, Diagnostics<()>> {
        self.expressions.resize(hir.expressions.len());
        self.statements.resize(hir.statements.len());

        let stmt = hir.statements.remove(hir.root).unwrap();
        let (ident, _, stmts) = stmt.into_namespace();

        // let namespace_id = self.namespaces.push(ident.id);
        // println!("{} -> {}", hir.identifiers.get(ident.id).unwrap(), namespace_id);
        self.transform_namespace(&mut hir, None, ident.id, stmts);

        debug_assert!(hir.expressions.is_empty(), "{:?}", hir.expressions);
        debug_assert!(hir.statements.is_empty(), "{:?}", hir.statements);

        Ok(Mir {
            functions: self.functions,
            structs: self.structs,
            identifiers: hir.identifiers,
            expressions: self.expressions,
            statements: self.statements,
            namespaces: self.namespaces,
            symbols: hir
                .symbols
                .into_iter()
                .filter_map(|(symbol_id, symbol)| {
                    if matches!(&symbol.kind, &HirSymbolKind::NotFound)
                        || matches!(&symbol.kind, &HirSymbolKind::Annotation(_, _))
                        || matches!(&symbol.kind, &HirSymbolKind::Namespace(..))
                    {
                        return None;
                    }

                    let ident_id = &match symbol.kind {
                        HirSymbolKind::NotFound => unreachable!(),
                        HirSymbolKind::Let(ident_id, _) => ident_id,
                        HirSymbolKind::LetFn(ident_id, _, _, _) => ident_id,
                        HirSymbolKind::Parameter(ident_id, _, _) => ident_id,
                        HirSymbolKind::Struct(ident_id, _) => ident_id,
                        HirSymbolKind::Field(ident_id, _, _) => ident_id,
                        HirSymbolKind::NativeType(ident_id, _) => ident_id,
                        HirSymbolKind::Native(ident_id, _, _, _) => ident_id,
                        HirSymbolKind::Annotation(ident_id, _) => ident_id,
                        HirSymbolKind::Namespace(ident_id, ..) => ident_id,
                    };

                    Some((
                        symbol_id,
                        Symbol {
                            id: symbol.id,
                            type_id: symbol.type_id,
                            ident_id: *ident_id,
                            kind: match symbol.kind {
                                HirSymbolKind::NotFound
                                | HirSymbolKind::Annotation(_, _)
                                | HirSymbolKind::Namespace(..) => {
                                    unreachable!()
                                }
                                HirSymbolKind::Let(_, _) => SymbolKind::Let,
                                HirSymbolKind::LetFn(_, _, params, ret_type_id) => {
                                    SymbolKind::LetFn(params, ret_type_id)
                                }
                                HirSymbolKind::Parameter(_, _, index) => {
                                    SymbolKind::Parameter(index)
                                }
                                HirSymbolKind::Struct(_, _) => SymbolKind::Struct,
                                HirSymbolKind::Field(ident_id, _, index) => {
                                    SymbolKind::Field(ident_id, index)
                                }
                                HirSymbolKind::NativeType(ident_id, t) => SymbolKind::NativeType(
                                    ident_id,
                                    match t {
                                        // todo:refactoring there is something to do about types
                                        //   (same code as for the types field)
                                        HirType::Invalid => unreachable!(),
                                        HirType::Boolean => Type::Boolean,
                                        HirType::Function(params, ret_type) => {
                                            Type::Function(params, ret_type)
                                        }
                                        HirType::Struct(_) => todo!(),
                                        HirType::Array(_, _) => todo!(),
                                        HirType::Number => Type::Number,
                                        HirType::Void => Type::Void,
                                        HirType::None => Type::None,
                                    },
                                ),
                                HirSymbolKind::Native(ident_id, params, ret_type_id, kind) => {
                                    SymbolKind::Native(ident_id, params, ret_type_id, kind)
                                }
                            },
                        },
                    ))
                })
                .collect::<VecMap<SymbolId, Symbol>>(),
            types: hir
                .types
                .into_iter()
                .filter_map(|(type_id, ty)| match ty {
                    HirType::Invalid => None,
                    HirType::Boolean => Some((type_id, Type::Boolean)),
                    HirType::Function(params, ret_type) => {
                        Some((type_id, Type::Function(params, ret_type)))
                    }
                    HirType::Struct(stmt_id) => {
                        let (symbol_id, struct_id) = self.structs_map[stmt_id];
                        Some((type_id, Type::Struct(symbol_id, struct_id)))
                    }
                    HirType::Array(value_type_id, len) => {
                        Some((type_id, Type::Array(value_type_id, len)))
                    }
                    HirType::Number => Some((type_id, Type::Number)),
                    HirType::Void => Some((type_id, Type::Void)),
                    HirType::None => Some((type_id, Type::None)),
                })
                .collect::<VecMap<TypeId, Type>>(),
        })
    }

    fn transform_namespace(
        &mut self,
        hir: &mut Hir,
        parent: Option<NamespaceId>,
        ident_id: IdentId,
        stmt_ids: Vec<StmtId>,
    ) {
        let namespace_id = self.namespaces.push((parent, ident_id));
        let current = ParentKind::Namespace(namespace_id);

        for stmt_id in stmt_ids.into_iter() {
            if let Some(stmt) = hir.statements.remove(stmt_id) {
                match stmt.kind {
                    HirStatementKind::Namespace(ident, _, statements) => {
                        // let namespace_id = self.namespaces.push(ident.id);
                        self.transform_namespace(hir, Some(namespace_id), ident.id, statements)
                    }
                    HirStatementKind::LetFn(
                        identifier,
                        _,
                        parameters,
                        ret_type,
                        implementation,
                        _,
                    ) => self.transform_function(
                        hir,
                        current,
                        stmt_id,
                        identifier,
                        parameters,
                        ret_type,
                        implementation,
                    ),
                    HirStatementKind::Struct(identifier, _, implementation, _) => {
                        self.transform_struct(current, stmt_id, identifier, implementation)
                    }
                    HirStatementKind::Annotation(_) => {
                        self.statements.remove(stmt_id);
                    }
                    kind => panic!(
                        "namespace, annotation, function or struct expected, got {:?}",
                        kind
                    ),
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_function(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        stmt_id: StmtId,
        identifier: HirIdentifier,
        parameters: Vec<HirParameter>,
        ret: HirReturn,
        implementation: Implementation<ExprId>,
    ) {
        let function_id = self.functions.create();

        self.fn_map.insert(stmt_id, function_id);

        let (expr_id, mutated_symbol_ids, mut variables) = match implementation {
            Implementation::Provided(expr_id) => {
                let is_void_fn = matches!(hir.types[ret.resolved_type_id()], HirType::Void);
                let expression = hir.expressions.remove(expr_id).unwrap();

                let (mutated_symbol_ids, variables) = self.transform_expression(
                    hir,
                    ParentKind::Function(function_id),
                    expression,
                    is_void_fn,
                );

                (Some(expr_id), mutated_symbol_ids, variables)
            }
            #[cfg(debug_assertions)]
            Implementation::Native(expr_id) => {
                let expression = hir.expressions.remove(expr_id).unwrap();
                if let HirExpressionKind::Block(stmt_ids) = expression.kind {
                    for stmt_id in stmt_ids {
                        hir.statements.remove(stmt_id);
                    }
                }
                (None, Default::default(), Default::default())
            }
            #[cfg(not(debug_assertions))]
            Implementation::Native => (None, Default::default(), Default::default()),
        };

        let parameters = parameters
            .into_iter()
            .map(|param| Parameter {
                symbol_id: param.resolved_symbol_id(),
                type_id: param.resolved_type_id(),
                mutable: mutated_symbol_ids.contains(&param.resolved_symbol_id()),
                identifier: param.identifier.into(),
            })
            .collect::<Vec<Parameter>>();

        for variable in variables.values_mut() {
            if mutated_symbol_ids.contains(&variable.symbol_id) {
                variable.mutable = true
            }
        }

        let function = Function {
            symbol_id: identifier.resolved_symbol_id(),
            identifier: identifier.into(),
            parameters,
            variables,
            body: expr_id,
            ret: ret.resolved_type_id(),
            parent,
        };

        self.functions.insert(function_id, function);
    }

    fn transform_struct(
        &mut self,
        parent: ParentKind,
        stmt_id: StmtId,
        identifier: HirIdentifier,
        implementation: Implementation<Vec<HirField>>,
    ) {
        let struct_id = self.structs.create();
        let symbol_id = identifier.resolved_symbol_id();
        self.structs.insert(
            struct_id,
            Struct {
                identifier: identifier.into(),
                symbol_id,
                fields: match implementation {
                    Implementation::Provided(fields) => Some(
                        fields
                            .into_iter()
                            .enumerate()
                            .map(|(index, field)| Field {
                                index,
                                symbol_id: field.resolved_symbol_id(),
                                type_id: field.resolved_type_id(),
                                identifier: field.identifier.into(),
                            })
                            .collect::<Vec<Field>>(),
                    ),
                    _ => None,
                },
                parent,
            },
        );
        self.structs_map.insert(stmt_id, (symbol_id, struct_id));
    }

    fn transform_expression(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expression: HirExpression,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let type_id = expression.resolved_type_id();

        match expression.kind {
            HirExpressionKind::Assignment(target, expr_id) => self.transform_assignment(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                target,
                expr_id,
                remove_implicit_rets,
            ),
            HirExpressionKind::If(cond_expr_id, true_expr_id, false_expr_id) => self.transform_if(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                cond_expr_id,
                true_expr_id,
                false_expr_id,
                remove_implicit_rets,
            ),
            HirExpressionKind::Literal(literal) => {
                self.transform_literal(hir, expression.id, expression.span, type_id, literal);
                (Default::default(), Default::default())
            }
            HirExpressionKind::Access(expr, ident_ref_id) => self.transform_access(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                expr,
                ident_ref_id,
                remove_implicit_rets,
            ),
            HirExpressionKind::FunctionCall(callee_expr_id, params) => self
                .transform_function_call(
                    hir,
                    parent,
                    expression.id,
                    expression.span,
                    type_id,
                    callee_expr_id,
                    params,
                    remove_implicit_rets,
                ),
            HirExpressionKind::While(cond_expr_id, body_expr_id) => self.transform_while(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                cond_expr_id,
                body_expr_id,
                remove_implicit_rets,
            ),
            HirExpressionKind::Block(stmt_ids) => self.transform_block(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                stmt_ids,
                remove_implicit_rets,
            ),
            HirExpressionKind::StructInstantiation(ident_ref_id, fields) => self
                .transform_struct_instantiation(
                    hir,
                    parent,
                    expression.id,
                    expression.span,
                    type_id,
                    ident_ref_id,
                    fields,
                    remove_implicit_rets,
                ),
            HirExpressionKind::ArrayInstantiation(values) => self.transform_array_instantiation(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                values,
                remove_implicit_rets,
            ),
            HirExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => self
                .transform_array_access(
                    hir,
                    parent,
                    expression.id,
                    expression.span,
                    type_id,
                    base_expr_id,
                    index_expr_id,
                    remove_implicit_rets,
                ),
        }
    }

    fn transform_literal(
        &mut self,
        hir: &mut Hir,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        literal: HirLiteral,
    ) {
        match literal.kind {
            HirLiteralKind::Boolean(b) => self.expressions.insert(
                expr_id,
                Expression {
                    id: expr_id,
                    kind: ExpressionKind::Literal(Literal {
                        kind: LiteralKind::Boolean(b),
                        span: literal.span,
                    }),
                    span,
                    type_id,
                },
            ),
            HirLiteralKind::Identifier(ident_ref_id) => self.expressions.insert(
                expr_id,
                Expression {
                    id: expr_id,
                    kind: ExpressionKind::Literal(Literal {
                        kind: LiteralKind::Identifier(
                            hir.identifier_refs[ident_ref_id].resolved_symbol_id(),
                        ),
                        span: literal.span,
                    }),
                    span,
                    type_id,
                },
            ),
            HirLiteralKind::Number(n) => self.expressions.insert(
                expr_id,
                Expression {
                    id: expr_id,
                    kind: ExpressionKind::Literal(Literal {
                        kind: LiteralKind::Number(n),
                        span: literal.span,
                    }),
                    span,
                    type_id,
                },
            ),
            HirLiteralKind::String(n) => self.expressions.insert(
                expr_id,
                Expression {
                    id: expr_id,
                    kind: ExpressionKind::Literal(Literal {
                        kind: LiteralKind::String(n),
                        span: literal.span,
                    }),
                    span,
                    type_id,
                },
            ),
        };
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_access(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        target_expr_id: ExprId,
        ident_ref_id: IdentRefId,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(target_expr_id).unwrap();
        self.transform_expression(hir, parent, expression, remove_implicit_rets);

        let symbol_id = hir.identifier_refs[ident_ref_id].resolved_symbol_id();

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::Access(target_expr_id, symbol_id),
                span,
                type_id,
            },
        );

        (Default::default(), Default::default())
    }

    /// Transform the assignment and return the mutated `SymbolId`
    #[allow(clippy::too_many_arguments)]
    fn transform_assignment(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        target: HirTarget,
        value_expr_id: ExprId,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(value_expr_id).unwrap();

        let (mut mutated_symbol_ids, mut variables) =
            self.transform_expression(hir, parent, expression, remove_implicit_rets);

        match target {
            HirTarget::Direct(ident_ref_id) => {
                let symbol_id = hir.identifier_refs[ident_ref_id].resolved_symbol_id();
                self.expressions.insert(
                    expr_id,
                    Expression {
                        id: expr_id,
                        kind: ExpressionKind::Assignment(Target::Direct(symbol_id), value_expr_id),
                        span,
                        type_id,
                    },
                );

                mutated_symbol_ids.push(symbol_id);
            }
            HirTarget::Indirect(target_expr_id) => {
                let expression = hir.expressions.remove(target_expr_id).unwrap();
                let (new_mutated_symbol_ids, new_variables) =
                    self.transform_expression(hir, parent, expression, remove_implicit_rets);

                self.expressions.insert(
                    expr_id,
                    Expression {
                        id: expr_id,
                        kind: ExpressionKind::Assignment(
                            Target::Indirect(target_expr_id),
                            value_expr_id,
                        ),
                        span,
                        type_id,
                    },
                );

                mutated_symbol_ids.extend(new_mutated_symbol_ids);
                variables.extend(new_variables);
            }
        }

        (mutated_symbol_ids, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_if(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        true_expr_id: ExprId,
        false_expr_id: Option<ExprId>,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) =
            self.transform_expression(hir, parent, expr, remove_implicit_rets);

        let expr = hir.expressions.remove(true_expr_id).unwrap();
        let (new_mutated_symbols_ids, new_variables) =
            self.transform_expression(hir, parent, expr, remove_implicit_rets);
        mutated_symbols_ids.extend(new_mutated_symbols_ids);
        variables.extend(new_variables);

        if let Some(false_expr_id) = false_expr_id {
            let expr = hir.expressions.remove(false_expr_id).unwrap();
            let (new_mutated_symbols_ids, new_variables) =
                self.transform_expression(hir, parent, expr, remove_implicit_rets);
            mutated_symbols_ids.extend(new_mutated_symbols_ids);
            variables.extend(new_variables);
        }

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::If(cond_expr_id, true_expr_id, false_expr_id),
                span,
                type_id,
            },
        );

        (mutated_symbols_ids, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_function_call(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        callee_expr_id: ExprId,
        mut params: Vec<ExprId>,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(callee_expr_id).unwrap();
        let (mut mutated_symbol_ids, mut variables) =
            self.transform_expression(hir, parent, expr, remove_implicit_rets);

        for expr_id in params.iter() {
            let expression = hir.expressions.remove(*expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression, remove_implicit_rets);
            mutated_symbol_ids.extend(new_mutated_symbol_ids);
            variables.extend(new_variables);
        }

        let expression = &self.expressions[callee_expr_id];
        let symbol_id = match &expression.kind {
            ExpressionKind::Literal(lit) => match &lit.kind {
                LiteralKind::Identifier(symbol_id) => *symbol_id,
                _ => panic!("Literal(Identifier) expected, got {expression:?}"),
            },
            ExpressionKind::Access(first_parameter, symbol_id) => {
                // todo add support for non-symbolic function calls (i.e. functions as values):
                //  if x { f1; } else { f2; }(...)

                // todo:refactoring maybe there is a better way to skip using a namespace as first
                //  parameter?
                if !matches!(
                    hir.types[self.expressions[*first_parameter].type_id],
                    HirType::Void
                ) {
                    params.insert(0, *first_parameter);
                }

                *symbol_id
            }
            _ => panic!("Literal(Literal) expected, got {expression:?}"),
        };

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::FunctionCall(symbol_id, params),
                span,
                type_id,
            },
        );

        (mutated_symbol_ids, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_while(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        body_expr_id: ExprId,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) =
            self.transform_expression(hir, parent, expr, remove_implicit_rets);

        let expr = hir.expressions.remove(body_expr_id).unwrap();
        let (new_mutated_symbols_ids, new_variables) =
            self.transform_expression(hir, parent, expr, remove_implicit_rets);
        mutated_symbols_ids.extend(new_mutated_symbols_ids);
        variables.extend(new_variables);

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::While(cond_expr_id, body_expr_id),
                span,
                type_id,
            },
        );

        (mutated_symbols_ids, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_block(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        stmt_ids: Vec<StmtId>,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut kept_stmt_ids = Vec::with_capacity(stmt_ids.len());
        let mut mutated_symbols = Vec::new();
        let mut variables = BTreeMap::new();

        for stmt_id in stmt_ids {
            let stmt = hir.statements.remove(stmt_id).unwrap();
            match stmt.kind {
                HirStatementKind::Expression(expr_id) => {
                    let (new_mutated_symbol_ids, new_variables) = self
                        .transform_expression_statement(
                            hir,
                            parent,
                            stmt.id,
                            stmt.span,
                            expr_id,
                            remove_implicit_rets,
                        );
                    mutated_symbols.extend(new_mutated_symbol_ids);
                    variables.extend(new_variables);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Let(ident, expr_id) => {
                    let new_variable = self.transform_let(
                        hir,
                        parent,
                        stmt_id,
                        stmt.span,
                        ident,
                        expr_id,
                        remove_implicit_rets,
                    );
                    variables.insert(new_variable.symbol_id, new_variable);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Ret(expr_id, mode) => {
                    mutated_symbols.extend(self.transform_ret(
                        hir,
                        parent,
                        stmt.id,
                        stmt.span.clone(),
                        expr_id,
                        mode,
                        remove_implicit_rets,
                    ));
                    kept_stmt_ids.push(stmt.id)
                }
                HirStatementKind::LetFn(identifier, _, parameters, ret_type, expr_id, _) => {
                    self.transform_function(
                        hir, parent, stmt_id, identifier, parameters, ret_type, expr_id,
                    );
                }
                HirStatementKind::Struct(identifier, _, fields, _) => {
                    self.transform_struct(parent, stmt_id, identifier, fields)
                }
                HirStatementKind::Annotation(_) | HirStatementKind::Use(_) => {
                    // nothing
                }
                HirStatementKind::Namespace(..) => todo!(),
            }
        }

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::Block(kept_stmt_ids),
                span,
                type_id,
            },
        );

        (mutated_symbols, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_struct_instantiation(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        ident_ref_id: IdentRefId,
        fields: Vec<(IdentRefId, ExprId)>,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut transformed_fields = Vec::with_capacity(fields.len());
        let mut mutated_symbol_ids = Vec::new();
        let mut variables = BTreeMap::new();

        for (field_ident_ref_id, field_expr_id) in fields.into_iter() {
            let expression = hir.expressions.remove(field_expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression, remove_implicit_rets);
            mutated_symbol_ids.extend(new_mutated_symbol_ids);
            variables.extend(new_variables);

            let field_index = match &hir.symbols
                [hir.identifier_refs[field_ident_ref_id].resolved_symbol_id()]
            .kind
            {
                HirSymbolKind::Field(_, _, index) => *index,
                _ => panic!("symbol must be a struct field"),
            };

            transformed_fields.push((
                field_index,
                hir.identifier_refs[field_ident_ref_id].resolved_symbol_id(),
                field_expr_id,
            ));
        }

        let stmt_id =
            *match &hir.symbols[hir.identifier_refs[ident_ref_id].resolved_symbol_id()].kind {
                HirSymbolKind::Struct(_, stmt_id) => stmt_id,
                _ => panic!("symbol must be a struct"),
            };

        if let Some(struct_stmt) = hir.statements.remove(stmt_id) {
            match struct_stmt.kind {
                HirStatementKind::Struct(identifier, _, implementation, fn_stmt_id) => {
                    if let Some(fn_stmt_id) = fn_stmt_id {
                        self.transform_function_rec(hir, parent, fn_stmt_id);
                    }

                    self.transform_struct(
                        fn_stmt_id
                            .map(|stmt_id| self.fn_map[stmt_id])
                            .map(ParentKind::Function)
                            .unwrap_or(parent),
                        struct_stmt.id,
                        identifier,
                        implementation,
                    )
                }
                _ => panic!("expected struct statement"),
            }
        }

        // we need to guarantee that the fields are sorted by declaration order
        transformed_fields.sort_by(|a, b| a.0.cmp(&b.0));

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::StructInstantiation(
                    self.structs_map[stmt_id].0,
                    self.structs_map[stmt_id].1,
                    transformed_fields
                        .into_iter()
                        .map(|(_, symbol_id, expr_id)| (symbol_id, expr_id))
                        .collect::<Vec<(SymbolId, ExprId)>>(),
                ),
                span,
                type_id,
            },
        );

        (mutated_symbol_ids, variables)
    }

    fn transform_function_rec(&mut self, hir: &mut Hir, parent: ParentKind, stmt_id: StmtId) {
        if let Some(fn_stmt) = hir.statements.remove(stmt_id) {
            match fn_stmt.kind {
                HirStatementKind::LetFn(
                    identifier,
                    _,
                    parameters,
                    ret,
                    implementation,
                    fn_stmt_id,
                ) => {
                    if let Some(fn_stmt_id) = fn_stmt_id {
                        self.transform_function_rec(hir, parent, fn_stmt_id);
                    }
                    self.transform_function(
                        hir,
                        fn_stmt_id
                            .map(|stmt_id| self.fn_map[stmt_id])
                            .map(ParentKind::Function)
                            .unwrap_or(parent),
                        stmt_id,
                        identifier,
                        parameters,
                        ret,
                        implementation,
                    )
                }
                _ => panic!("expected let fn struct statement"),
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_array_instantiation(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        values: Vec<ExprId>,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut transformed_values = Vec::with_capacity(values.len());

        let mut mutated_symbol_ids = Vec::new();
        let mut variables = BTreeMap::new();

        for value_expr_id in values.into_iter() {
            let expression = hir.expressions.remove(value_expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression, remove_implicit_rets);
            mutated_symbol_ids.extend(new_mutated_symbol_ids);
            variables.extend(new_variables);

            transformed_values.push(value_expr_id);
        }

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::ArrayInstantiation(transformed_values),
                span,
                type_id,
            },
        );

        (mutated_symbol_ids, variables)
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_array_access(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        base_expr_id: ExprId,
        index_expr_id: ExprId,
        remove_implcit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let base_expression = hir.expressions.remove(base_expr_id).unwrap();
        let (mut mutated_symbol_ids, mut variables) =
            self.transform_expression(hir, parent, base_expression, remove_implcit_rets);

        let index_expression = hir.expressions.remove(index_expr_id).unwrap();
        let (new_mutated_symbol_ids, new_variables) =
            self.transform_expression(hir, parent, index_expression, remove_implcit_rets);

        mutated_symbol_ids.extend(new_mutated_symbol_ids);
        variables.extend(new_variables);

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::ArrayAccess(base_expr_id, index_expr_id),
                span,
                type_id,
            },
        );

        (mutated_symbol_ids, variables)
    }

    fn transform_expression_statement(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        stmt_id: StmtId,
        span: Span,
        expr_id: ExprId,
        remove_implicit_rets: bool,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let res = self.transform_expression(hir, parent, expression, remove_implicit_rets);
        self.statements.insert(
            stmt_id,
            Statement {
                id: stmt_id,
                kind: StatementKind::Expression(expr_id),
                span,
            },
        );

        res
    }

    #[allow(clippy::too_many_arguments)]
    fn transform_let(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        stmt_id: StmtId,
        span: Span,
        identifier: HirIdentifier,
        expr_id: ExprId,
        remove_implicit_rets: bool,
    ) -> Variable {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let type_id = expression.resolved_type_id();
        let expr_span = expression.span.clone();
        let (mutated_symbol_ids, variables) =
            self.transform_expression(hir, parent, expression, remove_implicit_rets);

        assert!(mutated_symbol_ids.is_empty());
        assert!(variables.is_empty());

        let assignment_expr_id = self.expressions.create();
        self.expressions.insert(
            assignment_expr_id,
            Expression {
                id: assignment_expr_id,
                kind: ExpressionKind::Assignment(
                    Target::Direct(identifier.resolved_symbol_id()),
                    expr_id,
                ),
                span: expr_span, // not exactly that but close enough
                type_id,
            },
        );
        self.statements.insert(
            stmt_id,
            Statement {
                id: stmt_id,
                kind: StatementKind::Expression(assignment_expr_id),
                span,
            },
        );

        Variable {
            symbol_id: identifier.resolved_symbol_id(),
            identifier: identifier.into(),
            type_id,
            expression: expr_id,
            mutable: false, // todo:feature add `mut` keyword?
        }
    }

    /// Transform ret and return the list of mutated `SymbolId`s. If `remove_implicit_rets` is set,
    /// the `Ret(Some(expr), RetMode::Implicit)` is transformed to `{ expr; ret; }` and
    /// `Ret(None, RetMode::Implicit)` is transformed to `ret;`.
    #[allow(clippy::too_many_arguments)]
    fn transform_ret(
        &mut self,
        hir: &mut Hir,
        parent: ParentKind,
        stmt_id: StmtId,
        span: Span,
        expr_id: Option<ExprId>,
        mode: RetMode,
        remove_implicit_rets: bool,
    ) -> Vec<SymbolId> {
        let mutated_symbols = expr_id
            .map(|expr_id| {
                let expr = hir.expressions.remove(expr_id).unwrap();
                let (mutated_symbols, variables) =
                    self.transform_expression(hir, parent, expr, remove_implicit_rets);

                debug_assert!(variables.is_empty());
                mutated_symbols
            })
            .unwrap_or_default();

        if matches!(mode, RetMode::Implicit) && remove_implicit_rets {
            if let Some(expr_id) = expr_id {
                let expr_stmt_id = self.statements.create();
                self.statements.insert(
                    expr_stmt_id,
                    Statement {
                        id: expr_stmt_id,
                        kind: StatementKind::Expression(expr_id),
                        span: span.clone(),
                    },
                );

                let ret_stmt_id = self.statements.create();
                self.statements.insert(
                    ret_stmt_id,
                    Statement {
                        id: ret_stmt_id,
                        kind: StatementKind::Ret(None),
                        span: span.clone(),
                    },
                );

                let block_expr_id = self.expressions.create();
                self.expressions.insert(
                    block_expr_id,
                    Expression {
                        id: block_expr_id,
                        kind: ExpressionKind::Block(vec![expr_stmt_id, ret_stmt_id]),
                        span: span.clone(),
                        type_id: hir.void_type_id(),
                    },
                );

                self.statements.insert(
                    stmt_id,
                    Statement {
                        id: stmt_id,
                        kind: StatementKind::Expression(block_expr_id),
                        span,
                    },
                );
            } else {
                self.statements.insert(
                    stmt_id,
                    Statement {
                        id: stmt_id,
                        kind: StatementKind::Ret(None),
                        span: span.clone(),
                    },
                );
            }
        } else {
            self.statements.insert(
                stmt_id,
                Statement {
                    id: stmt_id,
                    kind: StatementKind::Ret(expr_id),
                    span,
                },
            );
        }

        mutated_symbols
    }
}

#[derive(Debug)]
pub struct Mir {
    pub functions: VecMap<FunctionId, Function>,
    pub structs: VecMap<StructId, Struct>,
    pub identifiers: VecMap<IdentId, String>,
    pub expressions: VecMap<ExprId, Expression>,
    pub statements: VecMap<StmtId, Statement>,
    pub namespaces: VecMap<NamespaceId, (Option<NamespaceId>, IdentId)>,
    pub symbols: VecMap<SymbolId, Symbol>,
    pub types: VecMap<TypeId, Type>,
}

impl TryFrom<Hir> for Mir {
    type Error = Diagnostics<()>;

    fn try_from(hir: Hir) -> Result<Self, Self::Error> {
        Transformer::new().transform(hir)
    }
}

#[derive(Debug)]
pub struct Function {
    pub identifier: Identifier,
    pub symbol_id: SymbolId,
    pub parameters: Vec<Parameter>,
    pub variables: BTreeMap<SymbolId, Variable>,
    pub body: Option<ExprId>,
    pub ret: TypeId,
    pub parent: ParentKind,
}

#[derive(Debug, Clone, Copy)]
pub enum ParentKind {
    Function(FunctionId),
    Namespace(NamespaceId),
}

#[derive(Debug)]
pub struct Identifier {
    pub id: IdentId,
    pub span: Span,
}

impl From<HirIdentifier> for Identifier {
    fn from(hir: HirIdentifier) -> Self {
        Identifier {
            id: hir.id,
            span: hir.span,
        }
    }
}

#[derive(Debug)]
pub struct Parameter {
    pub identifier: Identifier,
    pub symbol_id: SymbolId,
    pub type_id: TypeId,
    pub mutable: bool,
}

#[derive(Debug)]
pub struct Variable {
    pub identifier: Identifier,
    pub symbol_id: SymbolId,
    pub type_id: TypeId,
    pub expression: ExprId,
    pub mutable: bool,
}

#[derive(Debug)]
pub struct Struct {
    pub identifier: Identifier,
    pub symbol_id: SymbolId,
    // todo why not just a Vec<Field> that can be empty?
    pub fields: Option<Vec<Field>>,
    pub parent: ParentKind,
}

#[derive(Debug)]
pub struct Field {
    pub identifier: Identifier,
    pub index: usize,
    pub symbol_id: SymbolId,
    pub type_id: TypeId,
}

#[derive(Debug)]
pub struct IdentifierRef {
    pub id: IdentRefId,
    pub ident: Identifier,
}

impl From<HirIdentifierRef> for IdentifierRef {
    fn from(identifier_ref: HirIdentifierRef) -> Self {
        IdentifierRef {
            id: identifier_ref.id,
            ident: Identifier::from(identifier_ref.ident),
        }
    }
}

#[derive(Debug)]
pub struct Expression {
    pub id: ExprId,
    pub kind: ExpressionKind,
    pub span: Span,
    pub type_id: TypeId,
}

#[derive(Debug)]
pub enum ExpressionKind {
    Assignment(Target, ExprId),
    If(ExprId, ExprId, Option<ExprId>),
    Literal(Literal),
    Access(ExprId, SymbolId),
    FunctionCall(SymbolId, Vec<ExprId>),
    While(ExprId, ExprId),
    Block(Vec<StmtId>),
    // todo:refactoring only keep one of SymbolId or StructId? also, the field's SymbolId does not
    //   seem useful
    StructInstantiation(SymbolId, StructId, Vec<(SymbolId, ExprId)>),
    ArrayInstantiation(Vec<ExprId>),
    ArrayAccess(ExprId, ExprId),
}

#[derive(Debug)]
pub struct Literal {
    pub kind: LiteralKind,
    pub span: Span,
}

#[derive(Debug)]
pub enum LiteralKind {
    Boolean(bool),
    Identifier(SymbolId),
    Number(i64),
    String(String),
}

#[derive(Debug)]
pub enum Target {
    Direct(SymbolId),
    /// The expression id is of kind ExpressionKind::Access
    Indirect(ExprId),
}

#[derive(Debug)]
pub struct Statement {
    pub id: StmtId,
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StatementKind {
    Expression(ExprId),
    Ret(Option<ExprId>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Type {
    Boolean,
    Number,

    Function(Vec<TypeId>, TypeId),

    // todo:refactoring keep only one?
    Struct(SymbolId, StructId),
    Array(TypeId, usize),

    /// This value is used when the statement/expression does not have any value. This is the
    /// case for `let` and `let fn`.
    Void,

    /// This value is used when the statement/expression does not return any value. This is the
    /// case for `ret`.
    None,
}

#[derive(Debug)]
pub struct Symbol {
    pub id: SymbolId,
    pub kind: SymbolKind,
    pub type_id: TypeId,
    pub ident_id: IdentId,
}

#[derive(Debug, PartialEq)]
pub enum SymbolKind {
    Let,
    // todo:refactoring should we keep TypeId?
    LetFn(Vec<TypeId>, TypeId),
    Parameter(usize),
    Struct,
    // todo:refactoring do IdentId and usize make sense?
    Field(IdentId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, NativeFnKind),
}

#[cfg(test)]
mod tests {
    use crate::make_mir;
    use insta::assert_debug_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;
    use transmute_nst::nodes::Nst;

    macro_rules! t {
        ($name:ident => $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit: CompilationUnit = Default::default();

                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), &format!("{}\nnamespace core {{}}", $src)),
                )
                .parse();

                let hir = transmute_hir::resolve(Nst::from(compilation_unit.into_ast().unwrap()))
                    .unwrap();
                assert_debug_snapshot!(make_mir(hir));
            }
        };
    }

    t!(test_main => "let main() {}");
    t!(test_function_non_mut_param => "let f(a: number) {}");
    t!(test_function_mut_param => "let f(a: number) { a = a + 1; }");
    t!(test_function_local => "let f() { let a = 0; }");
    t!(test_function_local2 => "let f() { let a = 0; let b = 1 ; }");
    t!(test_function_native => "namespace std { annotation native; } @std.native let f() { }");
    t!(test_struct_native => "namespace std { annotation native; } @std.native struct S { }");
    t!(test_function_mut_local => "let f() { let a = 0; a = 1; }");
    t!(test_function_mut_local_shadow_param => "let f(a: number) { let a = 0; a = 1; }");
    t!(test_if => "let f() { if true { } else { } }");
    t!(test_while => "let f() { while true { 1; } }");
    t!(test_expression_in_block => "let f() { if true { 1; } }");
    t!(test_inner_function => "let f(): number { let g(): boolean { true; }; 1; }");
    t!(test_struct => "struct Struct { field: number }");
    t!(test_inner_struct => "let f() { struct Struct { field: number } }");
    t!(test_structs_same_field_names => r#"
        struct Inner { field: number }
        struct Outer { field: Inner }
    "#);
    t!(test_struct_instantiation => r#"
        struct Struct { field: number }
        let f() {
            let s = Struct { field: 1 };
        }
    "#);
    t!(test_struct_instantiation_nested => r#"
        struct Inner { field: number };
        struct Outer { inner: Inner };
        let f() {
            let s = Outer { inner: Inner { field: 1 } };
        }
    "#);
    t!(test_struct_instantiation_fields_out_of_order => r#"
        struct Struct { field1: number, field2: boolean }
        let f() {
            let s = Struct { field2: true, field1: 1 };
        }
    "#);
    t!(test_struct_field_read => r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct { field: 1 };
            s.field;
        }
    "#);
    t!(test_struct_field_write => r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct {
                field: 1
            };

            s.field = 2;

            1;
        }
    "#);
    t!(test_array_instantiate => r#"
        let f() {
            let a = [1, 2];
        }
    "#);
    t!(test_array_access => r#"
        let f() {
            let a = [1, 2];
            let b = a[0];
        }
    "#);
    t!(test_array_instantiate_and_access => r#"
        let f() {
            [1, 2][0];
        }
    "#);
    t!(test_namespaced_function_call => r#"
        namespace ns {
            let f() {}
        }
        let main() {
            ns.f();
        }
    "#);
    t!(test_use_outside_function => r#"
        namespace ns1 {
            let f() {}
        }
        namespace ns2 {
            use ns1.f;
            let g() {
                f();
            }
        }
    "#);
    t!(test_use_inside_function => r#"
        namespace ns {
            let f() {}
        }
        let main() {
            use ns.f;
            f();
        }
    "#);
    // todo replicate the ones from hir
    // t!(test_function_call_on_value => r#"
    //     let print(n: number) {}
    //     let f() {
    //         1.print();
    //     }
    // "#);
}
