use std::collections::BTreeMap;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{
    ExprId, FunctionId, IdentId, IdentRefId, StmtId, StructId, SymbolId, TypeId,
};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;
use transmute_hir::expression::{ExpressionKind as HirExpressionKind, Target as HirTarget};
use transmute_hir::literal::{Literal as HirLiteral, LiteralKind as HirLiteralKind};
use transmute_hir::natives::Type as HirType;
use transmute_hir::statement::StatementKind as HirStatementKind;
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

pub fn make_mir(hir: Hir) -> Result<Mir, Diagnostics> {
    Mir::try_from(hir)
}

struct Transformer {
    functions: VecMap<FunctionId, Function>,
    structs: VecMap<StructId, Struct>,
    // todo:refactoring only keep one of SymbolId or StructId?
    structs_map: VecMap<StmtId, (SymbolId, StructId)>,
    expressions: VecMap<ExprId, Expression>,
    statements: VecMap<StmtId, Statement>,
}

impl Transformer {
    pub fn new() -> Self {
        Self {
            functions: Default::default(),
            structs: Default::default(),
            structs_map: Default::default(),
            expressions: Default::default(),
            statements: Default::default(),
        }
    }

    pub fn transform(mut self, mut hir: Hir) -> Result<Mir, Diagnostics> {
        self.expressions.resize(hir.expressions.len());
        self.statements.resize(hir.statements.len());

        for stmt_id in hir.roots.clone().into_iter() {
            let stmt = hir.statements.remove(stmt_id).unwrap();

            match stmt.kind {
                HirStatementKind::LetFn(identifier, _, parameters, ret_type, expr_id) => self
                    .transform_function(&mut hir, None, identifier, parameters, ret_type, expr_id),
                HirStatementKind::Struct(identifier, _, fields) => {
                    self.transform_struct(None, stmt_id, identifier, fields)
                }
                HirStatementKind::Annotation(_) => {
                    self.statements.remove(stmt_id);
                }
                kind => panic!("function or struct expected, got {:?}", kind),
            }
        }

        debug_assert!(hir.expressions.is_empty(), "{:?}", hir.expressions);
        debug_assert!(hir.statements.is_empty(), "{:?}", hir.statements);

        Ok(Mir {
            functions: self.functions,
            structs: self.structs,
            identifiers: hir.identifiers,
            expressions: self.expressions,
            statements: self.statements,
            symbols: hir
                .symbols
                .into_iter()
                .filter_map(|(symbol_id, symbol)| {
                    if matches!(&symbol.kind, &HirSymbolKind::NotFound)
                        || matches!(&symbol.kind, &HirSymbolKind::Annotation(_, _))
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
                    };

                    Some((
                        symbol_id,
                        Symbol {
                            id: symbol.id,
                            type_id: symbol.type_id,
                            ident_id: *ident_id,
                            kind: match symbol.kind {
                                HirSymbolKind::NotFound | HirSymbolKind::Annotation(_, _) => {
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
                                        HirType::String => Type::String,
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
                    HirType::String => Some((type_id, Type::String)),
                    HirType::Void => Some((type_id, Type::Void)),
                    HirType::None => Some((type_id, Type::None)),
                })
                .collect::<VecMap<TypeId, Type>>(),
        })
    }

    fn transform_function(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        identifier: HirIdentifier,
        parameters: Vec<HirParameter>,
        ret: HirReturn,
        implementation: Implementation,
    ) {
        let function_id = self.functions.create();

        let (expr_id, mutated_symbol_ids, mut variables) = match implementation {
            Implementation::Provided(expr_id) => {
                let expression = hir.expressions.remove(expr_id).unwrap();

                let (mutated_symbol_ids, variables) =
                    self.transform_expression(hir, Some(function_id), expression);

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
        parent: Option<FunctionId>,
        stmt_id: StmtId,
        identifier: HirIdentifier,
        fields: Vec<HirField>,
    ) {
        let struct_id = self.structs.create();
        let symbol_id = identifier.resolved_symbol_id();
        self.structs.insert(
            struct_id,
            Struct {
                identifier: identifier.into(),
                symbol_id,
                fields: fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, field)| Field {
                        index,
                        symbol_id: field.resolved_symbol_id(),
                        type_id: field.resolved_type_id(),
                        identifier: field.identifier.into(),
                    })
                    .collect::<Vec<Field>>(),
                parent,
            },
        );
        self.structs_map.insert(stmt_id, (symbol_id, struct_id));
    }

    fn transform_expression(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        expression: HirExpression,
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
            ),
            HirExpressionKind::FunctionCall(ident_ref_id, params) => self.transform_function_call(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                ident_ref_id,
                params,
            ),
            HirExpressionKind::While(cond_expr_id, body_expr_id) => self.transform_while(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                cond_expr_id,
                body_expr_id,
            ),
            HirExpressionKind::Block(stmt_ids) => self.transform_block(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                stmt_ids,
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
                ),
            HirExpressionKind::ArrayInstantiation(values) => self.transform_array_instantiation(
                hir,
                parent,
                expression.id,
                expression.span,
                type_id,
                values,
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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        target_expr_id: ExprId,
        ident_ref_id: IdentRefId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(target_expr_id).unwrap();
        self.transform_expression(hir, parent, expression);

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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        target: HirTarget,
        value_expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(value_expr_id).unwrap();

        let (mut mutated_symbol_ids, mut variables) =
            self.transform_expression(hir, parent, expression);

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
                    self.transform_expression(hir, parent, expression);

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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        true_expr_id: ExprId,
        false_expr_id: Option<ExprId>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) = self.transform_expression(hir, parent, expr);

        let expr = hir.expressions.remove(true_expr_id).unwrap();
        let (new_mutated_symbols_ids, new_variables) = self.transform_expression(hir, parent, expr);
        mutated_symbols_ids.extend(new_mutated_symbols_ids);
        variables.extend(new_variables);

        if let Some(false_expr_id) = false_expr_id {
            let expr = hir.expressions.remove(false_expr_id).unwrap();
            let (new_mutated_symbols_ids, new_variables) =
                self.transform_expression(hir, parent, expr);
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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        ident_ref_id: IdentRefId,
        params: Vec<ExprId>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut mutated_symbol_ids = Vec::new();
        let mut variables = BTreeMap::new();

        let symbol_id = hir.identifier_refs[ident_ref_id].resolved_symbol_id();

        for expr_id in params.iter() {
            let expression = hir.expressions.remove(*expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression);
            mutated_symbol_ids.extend(new_mutated_symbol_ids);
            variables.extend(new_variables);
        }

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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        body_expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) = self.transform_expression(hir, parent, expr);

        let expr = hir.expressions.remove(body_expr_id).unwrap();
        let (new_mutated_symbols_ids, new_variables) = self.transform_expression(hir, parent, expr);
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

    fn transform_block(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        stmt_ids: Vec<StmtId>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut kept_stmt_ids = Vec::with_capacity(stmt_ids.len());
        let mut mutated_symbols = Vec::new();
        let mut variables = BTreeMap::new();

        for stmt_id in stmt_ids {
            let stmt = hir.statements.remove(stmt_id).unwrap();
            match stmt.kind {
                HirStatementKind::Expression(expr_id) => {
                    let (new_mutated_symbol_ids, new_variables) = self
                        .transform_expression_statement(hir, parent, stmt.id, stmt.span, expr_id);
                    mutated_symbols.extend(new_mutated_symbol_ids);
                    variables.extend(new_variables);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Let(ident, expr_id) => {
                    let new_variable =
                        self.transform_let(hir, parent, stmt_id, stmt.span, ident, expr_id);
                    variables.insert(new_variable.symbol_id, new_variable);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Ret(expr_id, _) => {
                    mutated_symbols.extend(self.transform_ret(
                        hir,
                        parent,
                        stmt.id,
                        stmt.span.clone(),
                        expr_id,
                    ));
                    kept_stmt_ids.push(stmt.id)
                }
                HirStatementKind::LetFn(identifier, _, parameters, ret_type, expr_id) => {
                    self.transform_function(hir, parent, identifier, parameters, ret_type, expr_id);
                }
                HirStatementKind::Struct(identifier, _, fields) => {
                    self.transform_struct(parent, stmt_id, identifier, fields)
                }
                HirStatementKind::Annotation(_) => {
                    // nothing
                }
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
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        ident_ref_id: IdentRefId,
        fields: Vec<(IdentRefId, ExprId)>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut transformed_fields = Vec::with_capacity(fields.len());
        let mut mutated_symbol_ids = Vec::new();
        let mut variables = BTreeMap::new();

        for (field_ident_ref_id, field_expr_id) in fields.into_iter() {
            let expression = hir.expressions.remove(field_expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression);
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
            match &hir.symbols[hir.identifier_refs[ident_ref_id].resolved_symbol_id()].kind {
                HirSymbolKind::Struct(_, stmt_id) => stmt_id,
                _ => panic!("symbol must be a struct"),
            };

        // we need to guarantee that the fields are sorted by declaration order
        transformed_fields.sort_by(|a, b| a.0.cmp(&b.0));

        self.expressions.insert(
            expr_id,
            Expression {
                id: expr_id,
                kind: ExpressionKind::StructInstantiation(
                    self.structs_map[*stmt_id].0,
                    self.structs_map[*stmt_id].1,
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

    fn transform_array_instantiation(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        values: Vec<ExprId>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let mut transformed_values = Vec::with_capacity(values.len());

        let mut mutated_symbol_ids = Vec::new();
        let mut variables = BTreeMap::new();

        for value_expr_id in values.into_iter() {
            let expression = hir.expressions.remove(value_expr_id).unwrap();
            let (new_mutated_symbol_ids, new_variables) =
                self.transform_expression(hir, parent, expression);
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

    fn transform_array_access(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        base_expr_id: ExprId,
        index_expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let base_expression = hir.expressions.remove(base_expr_id).unwrap();
        let (mut mutated_symbol_ids, mut variables) =
            self.transform_expression(hir, parent, base_expression);

        let index_expression = hir.expressions.remove(index_expr_id).unwrap();
        let (new_mutated_symbol_ids, new_variables) =
            self.transform_expression(hir, parent, index_expression);

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
        parent: Option<FunctionId>,
        stmt_id: StmtId,
        span: Span,
        expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let res = self.transform_expression(hir, parent, expression);

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

    fn transform_let(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        stmt_id: StmtId,
        span: Span,
        identifier: HirIdentifier,
        expr_id: ExprId,
    ) -> Variable {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let type_id = expression.resolved_type_id();
        let expr_span = expression.span.clone();
        let (mutated_symbol_ids, variables) = self.transform_expression(hir, parent, expression);

        assert!(mutated_symbol_ids.is_empty());
        assert!(variables.is_empty());

        let assignment_expr_id = ExprId::from(self.expressions.len());
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

    /// Transform ret and return the list of mutated `SymbolId`s
    fn transform_ret(
        &mut self,
        hir: &mut Hir,
        parent: Option<FunctionId>,
        stmt_id: StmtId,
        span: Span,
        expr_id: Option<ExprId>,
    ) -> Vec<SymbolId> {
        let mutated_symbols = expr_id
            .map(|expr_id| {
                let expr = hir.expressions.remove(expr_id).unwrap();
                let (mutated_symbols, variables) = self.transform_expression(hir, parent, expr);

                debug_assert!(variables.is_empty());
                mutated_symbols
            })
            .unwrap_or_default();

        self.statements.insert(
            stmt_id,
            Statement {
                id: stmt_id,
                kind: StatementKind::Ret(expr_id),
                span,
            },
        );

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
    pub symbols: VecMap<SymbolId, Symbol>,
    pub types: VecMap<TypeId, Type>,
}

impl TryFrom<Hir> for Mir {
    type Error = Diagnostics;

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
    pub parent: Option<FunctionId>,
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
    pub fields: Vec<Field>,
    pub parent: Option<FunctionId>,
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
    String,

    Function(Vec<TypeId>, TypeId),

    // todo:refactoring keep ony one?
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

    #[test]
    fn test_main() {
        let ast = transmute_ast::parse("let main() {}").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_non_mut_param() {
        let ast = transmute_ast::parse("let f(a: number) {}").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_mut_param() {
        let ast = transmute_ast::parse("let f(a: number) { a = a + 1; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_local() {
        let ast = transmute_ast::parse("let f() { let a = 0; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_local2() {
        let ast = transmute_ast::parse("let f() { let a = 0; let b = 1 ; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_native() {
        let ast = transmute_ast::parse("annotation native; @native let f() { }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_mut_local() {
        let ast = transmute_ast::parse("let f() { let a = 0; a = 1; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_function_mut_local_shadow_param() {
        let ast = transmute_ast::parse("let f(a: number) { let a = 0; a = 1; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_if() {
        let ast = transmute_ast::parse("let f() { if true { } else { } }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_while() {
        let ast = transmute_ast::parse("let f() { while true { 1; } }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_expression_in_block() {
        let ast = transmute_ast::parse("let f() { if true { 1; } }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_inner_function() {
        let ast =
            transmute_ast::parse("let f(): number { let g(): boolean { true; }; 1; }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct() {
        let ast = transmute_ast::parse("struct Struct { field: number }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_inner_struct() {
        let ast = transmute_ast::parse("let f() { struct Struct { field: number } }").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_structs_same_field_names() {
        let ast = transmute_ast::parse(
            r#"
            struct Inner { field: number }
            struct Outer { field: Inner }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct_instantiation() {
        let ast = transmute_ast::parse(
            r#"
                struct Struct { field: number }
                let f() {
                    let s = Struct { field: 1 };
                }
                "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct_instantiation_nested() {
        let ast = transmute_ast::parse(
            r#"
                struct Inner { field: number };
                struct Outer { inner: Inner };
                let f() {
                    let s = Outer { inner: Inner { field: 1 } };
                }
                "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct_instantiation_fields_out_of_order() {
        let ast = transmute_ast::parse(
            r#"
                struct Struct { field1: number, field2: boolean }
                let f() {
                    let s = Struct { field2: true, field1: 1 };
                }
                "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct_field_read() {
        let ast = transmute_ast::parse(
            r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct { field: 1 };
            s.field;
        }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_struct_field_write() {
        let ast = transmute_ast::parse(
            r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct {
                field: 1
            };

            s.field = 2;

            1;
        }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_array_instantiate() {
        let ast = transmute_ast::parse(
            r#"
        let f() {
            let a = [1, 2];
        }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_array_access() {
        let ast = transmute_ast::parse(
            r#"
        let f() {
            let a = [1, 2];
            let b = a[0];
        }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_array_instantiate_and_access() {
        let ast = transmute_ast::parse(
            r#"
        let f() {
            [1, 2][0];
        }
        "#,
        )
        .unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }
}
