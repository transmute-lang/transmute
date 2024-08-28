#![allow(unused)]

use std::any::type_name;
use std::collections::BTreeMap;
use std::env::var;
use std::thread::available_parallelism;
use transmute_core::error::{Diagnostic, Diagnostics, Level};
use transmute_core::id;
use transmute_core::ids::{
    ExprId, FunctionId, IdentId, IdentRefId, StmtId, StructId, SymbolId, TypeId,
};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;
use transmute_hir::bound::{Bound, BoundState};
use transmute_hir::expression::{ExpressionKind as HirExpressionKind, Target as HirTarget};
use transmute_hir::literal::{Literal as HirLiteral, LiteralKind as HirLiteralKind};
use transmute_hir::natives::Type as HirType;
use transmute_hir::statement::{Field, RetMode, Return, StatementKind as HirStatementKind};
use transmute_hir::symbol::{Symbol as HirSymbol, SymbolKind as HirSymbolKind};
use transmute_hir::typed::{Typed, TypedState};
use transmute_hir::{
    ResolvedExpression as HirExpression, ResolvedIdentifier as HirIdentifier,
    ResolvedIdentifierRef as HirIdentifierRef, ResolvedParameter as HirParameter,
    ResolvedStatement as HirStatement,
};
use transmute_hir::{ResolvedHir as Hir, ResolvedReturn as HirReturn};

// todo move to MIR?
pub use transmute_hir::natives::NativeFnKind;

pub fn make_mir(hir: Hir) -> Result<Mir, Diagnostics> {
    Mir::try_from(hir)
}

struct Transformer {
    functions: VecMap<FunctionId, Function>,
    structs: VecMap<StructId, Struct>,
    expressions: VecMap<ExprId, Expression>,
    statements: VecMap<StmtId, Statement>,
}

impl Transformer {
    pub fn new() -> Self {
        Self {
            functions: Default::default(),
            structs: Default::default(),
            expressions: Default::default(),
            statements: Default::default(),
        }
    }

    pub fn transform(mut self, mut hir: Hir) -> Result<Mir, Diagnostics> {
        let mut diagnostics = Diagnostics::default();

        self.expressions.resize(hir.expressions.len());
        self.statements.resize(hir.statements.len());

        for stmt_id in hir.roots.clone().iter() {
            let stmt = hir.statements.remove(*stmt_id).unwrap();

            match stmt.kind {
                HirStatementKind::LetFn(identifier, parameters, ret_type, expr_id) => {
                    self.transform_function(&mut hir, identifier, parameters, ret_type, expr_id)
                }
                HirStatementKind::Struct(_, _) => todo!(),
                _ => {
                    // todo it seems that roots is an useless concept outside of the interpreter flow. think
                    //   about what to do about it
                    diagnostics.push(Diagnostic::new(
                        "only functions are allowed at top level",
                        stmt.span,
                        Level::Error,
                        (file!(), line!()),
                    ))
                }
            }
        }

        if !diagnostics.is_empty() {
            return Err(diagnostics);
        }

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
                    if matches!(&symbol.kind, &HirSymbolKind::NotFound) {
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
                    };
                    Some((
                        symbol_id,
                        Symbol {
                            id: symbol.id,
                            type_id: symbol.type_id,
                            ident_id: *ident_id,
                            kind: match symbol.kind {
                                HirSymbolKind::NotFound => unreachable!(),
                                HirSymbolKind::Let(_, stmt_id) => SymbolKind::Let(stmt_id),
                                HirSymbolKind::LetFn(_, stmt_id, params, ret_type_id) => {
                                    SymbolKind::LetFn(stmt_id, params, ret_type_id)
                                }
                                HirSymbolKind::Parameter(_, stmt_id, index) => {
                                    SymbolKind::Parameter(stmt_id, index)
                                }
                                HirSymbolKind::Struct(_, stmt_id) => SymbolKind::Struct(stmt_id),
                                HirSymbolKind::Field(_, stmt_id, index) => {
                                    SymbolKind::Field(stmt_id, index)
                                }
                                HirSymbolKind::NativeType(ident_id, t) => SymbolKind::NativeType(
                                    ident_id,
                                    match t {
                                        // todo there is something to do about types (same code as
                                        //   for the types field)
                                        HirType::Invalid => unreachable!(),
                                        HirType::Boolean => Type::Boolean,
                                        HirType::Function(params, ret_type) => {
                                            Type::Function(params, ret_type)
                                        }
                                        HirType::Struct(_) => todo!(),
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
                    HirType::Struct(_) => Some((type_id, todo!())),
                    HirType::Number => Some((type_id, Type::Number)),
                    HirType::Void => Some((type_id, Type::Void)),
                    HirType::None => Some((type_id, Type::None)),
                })
                .collect::<VecMap<TypeId, Type>>(),
        })
    }

    fn transform_function(
        &mut self,
        hir: &mut Hir,
        identifier: HirIdentifier,
        parameters: Vec<HirParameter>,
        ret: HirReturn,
        expr_id: ExprId,
    ) {
        let function_id = FunctionId::from(self.functions.len());

        let expression = hir.expressions.remove(expr_id).unwrap();
        let (mutated_symbol_ids, mut variables) = self.transform_expression(hir, expression);

        let parameters = parameters
            .into_iter()
            .map(|param| Parameter {
                symbol_id: param.resolved_symobl_id(),
                type_id: param.resolved_type_id(),
                mutable: mutated_symbol_ids.contains(&param.resolved_symobl_id()),
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
        };

        self.functions.insert(function_id, function);
    }

    fn transform_expression(
        &mut self,
        hir: &mut Hir,
        expression: HirExpression,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let type_id = expression.resolved_type_id();

        match expression.kind {
            HirExpressionKind::Assignment(target, expr_id) => self.transform_assignment(
                hir,
                expression.id,
                expression.span,
                type_id,
                target,
                expr_id,
            ),
            HirExpressionKind::If(cond_expr_id, true_expr_id, false_expr_id) => self.transform_if(
                hir,
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
            HirExpressionKind::Access(_, _) => todo!(),
            HirExpressionKind::FunctionCall(ident_ref_id, params) => self.transform_function_call(
                hir,
                expression.id,
                expression.span,
                type_id,
                ident_ref_id,
                params,
            ),
            HirExpressionKind::While(cond_expr_id, body_expr_id) => self.transform_while(
                hir,
                expression.id,
                expression.span,
                type_id,
                cond_expr_id,
                body_expr_id,
            ),
            HirExpressionKind::Block(stmt_ids) => {
                self.transform_block(hir, expression.id, expression.span, type_id, stmt_ids)
            }
            HirExpressionKind::StructInstantiation(_, _) => todo!(),
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
        };
    }

    /// Transform the assignment and return the mutated `SymbolId`
    fn transform_assignment(
        &mut self,
        hir: &mut Hir,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        target: HirTarget,
        value_expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(value_expr_id).unwrap();

        let (mut mutated_symbol_ids, variables) = self.transform_expression(hir, expression);

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
                (mutated_symbol_ids, variables)
            }
            HirTarget::Indirect(_) => todo!(),
        }
    }

    fn transform_if(
        &mut self,
        hir: &mut Hir,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        true_expr_id: ExprId,
        false_expr_id: Option<ExprId>,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) = self.transform_expression(hir, expr);

        let expr = hir.expressions.remove(true_expr_id).unwrap();
        let (mut new_mutated_symbols_ids, new_variables) = self.transform_expression(hir, expr);
        mutated_symbols_ids.append(&mut new_mutated_symbols_ids);
        variables.extend(new_variables);

        if let Some(false_expr_id) = false_expr_id {
            let expr = hir.expressions.remove(false_expr_id).unwrap();
            let (mut new_mutated_symbols_ids, new_variables) = self.transform_expression(hir, expr);
            mutated_symbols_ids.append(&mut new_mutated_symbols_ids);
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

    fn transform_function_call(
        &mut self,
        hir: &mut Hir,
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
            let (mut new_mutated_symbol_ids, mut new_variables) =
                self.transform_expression(hir, expression);
            mutated_symbol_ids.append(&mut new_mutated_symbol_ids);
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

    fn transform_while(
        &mut self,
        hir: &mut Hir,
        expr_id: ExprId,
        span: Span,
        type_id: TypeId,
        cond_expr_id: ExprId,
        body_expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expr = hir.expressions.remove(cond_expr_id).unwrap();
        let (mut mutated_symbols_ids, mut variables) = self.transform_expression(hir, expr);

        let expr = hir.expressions.remove(body_expr_id).unwrap();
        let (mut new_mutated_symbols_ids, new_variables) = self.transform_expression(hir, expr);
        mutated_symbols_ids.append(&mut new_mutated_symbols_ids);
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
                    let (mut new_mutated_symbol_ids, new_variables) =
                        self.transform_expression_statement(hir, stmt.id, stmt.span, expr_id);
                    mutated_symbols.append(&mut new_mutated_symbol_ids);
                    variables.extend(new_variables);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Let(ident, expr_id) => {
                    let new_variable = self.transform_let(hir, stmt_id, stmt.span, ident, expr_id);
                    variables.insert(new_variable.symbol_id, new_variable);
                    kept_stmt_ids.push(stmt.id);
                }
                HirStatementKind::Ret(expr_id, _) => {
                    mutated_symbols.append(&mut self.transform_ret(
                        hir,
                        stmt.id,
                        stmt.span.clone(),
                        expr_id,
                    ));
                    kept_stmt_ids.push(stmt.id)
                }
                HirStatementKind::LetFn(_, _, _, _) => todo!(),
                HirStatementKind::Struct(_, _) => todo!(),
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

    fn transform_expression_statement(
        &mut self,
        hir: &mut Hir,
        stmt_id: StmtId,
        span: Span,
        expr_id: ExprId,
    ) -> (Vec<SymbolId>, BTreeMap<SymbolId, Variable>) {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let res = self.transform_expression(hir, expression);

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
        stmt_id: StmtId,
        span: Span,
        identifier: HirIdentifier,
        expr_id: ExprId,
    ) -> Variable {
        let expression = hir.expressions.remove(expr_id).unwrap();
        let type_id = expression.resolved_type_id();
        let expr_span = expression.span.clone();
        let (mutated_symbol_ids, variables) = self.transform_expression(hir, expression);

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
            mutable: false, // todo add `mut` keyword?
        }
    }

    /// Transform ret and return the list of mutated `SymbolId`s
    fn transform_ret(
        &mut self,
        hir: &mut Hir,
        stmt_id: StmtId,
        span: Span,
        expr_id: ExprId,
    ) -> Vec<SymbolId> {
        let expr = hir.expressions.remove(expr_id).unwrap();
        let (mutated_symbols, variables) = self.transform_expression(hir, expr);

        debug_assert!(variables.is_empty());

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
    pub body: ExprId,
    pub ret: TypeId,
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
    // todo
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
    StructInstantiation(SymbolId, Vec<(SymbolId, ExprId)>),
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
    Ret(ExprId),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Type {
    Boolean,
    Function(Vec<TypeId>, TypeId),
    Struct(StructId),
    Number,

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
    Let(StmtId),
    LetFn(StmtId, Vec<TypeId>, TypeId),
    // todo could StmtId be replaced with SymbolId (the symbol that defines the function)
    Parameter(StmtId, usize),
    Struct(StmtId),
    // todo could StmtId be replaced with SymbolId (the symbol that defines the struct)
    Field(StmtId, usize),
    NativeType(IdentId, Type),
    Native(IdentId, Vec<TypeId>, TypeId, NativeFnKind),
}

#[cfg(test)]
mod tests {
    use crate::make_mir;
    use insta::assert_debug_snapshot;

    #[test]
    fn test_main_with_free_statements() {
        let ast = transmute_ast::parse("let main() {}; let a = 1;").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_free_statements_without_main() {
        let ast = transmute_ast::parse("let a = 1;").unwrap();
        let hir = transmute_hir::resolve(ast).unwrap();
        assert_debug_snapshot!(make_mir(hir));
    }

    #[test]
    fn test_main_without_free_statements() {
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
}