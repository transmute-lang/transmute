use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeId};
use crate::ast::literal::LiteralKind;
use crate::ast::operators::{BinaryOperator, BinaryOperatorKind, UnaryOperator};
use crate::ast::statement::{Field, Parameter, StatementKind};
use crate::ast::Ast;
use crate::error::{Diagnostic, Diagnostics};
use crate::exit_points::{ExitPoint, ExitPoints};
use crate::interpreter::Value;
use crate::lexer::Span;
use crate::natives;
use crate::natives::{NativeType, Natives};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

pub struct Resolver {
    ast: Ast,
    symbols: Rc<RefCell<Vec<Symbol>>>,
    types: RefCell<Vec<Type>>,
    type_bindings: HashMap<Typed, Result<TypeId, ()>>,
    diagnostics: Diagnostics,
    scope_stack: Vec<Scope>,
}

impl Resolver {
    pub fn new(ast: Ast, natives: Natives) -> Self {
        let ast = ast.merge(Into::<Ast>::into(&natives));
        let symbols = Rc::new(RefCell::new(Vec::<Symbol>::new()));
        let mut me = Self {
            ast,
            symbols: symbols.clone(),
            types: Default::default(),
            type_bindings: Default::default(),
            diagnostics: Default::default(),
            scope_stack: vec![Scope::new(symbols)],
        };

        let (native_functions, native_types) = natives.iterators();

        for native in native_types {
            let ident = me.ast.identifier_id(native.name());
            me.insert_symbol(
                ident,
                SymbolKind::NativeType(native),
                me.type_id(Type::None),
            );
        }

        let dummy_span = Span::new(1, 1, 0, 0);

        for native in native_functions {
            let ident = me.ast.identifier_id(native.name());

            let ret_type = me
                .resolve_type(me.ast.identifier_id(native.return_type()), &dummy_span)
                .expect("native function is valid");

            let param_types = native
                .parameters()
                .iter()
                .map(|p| {
                    me.resolve_type(me.ast.identifier_id(p), &dummy_span)
                        .expect("native function is valid")
                })
                .collect::<Vec<TypeId>>();

            me.insert_symbol(
                ident,
                SymbolKind::NativeFn(ident, param_types, ret_type, native.body()),
                ret_type,
            );
        }

        me
    }

    pub fn resolve(mut self) -> Result<(Ast, Vec<Symbol>, Types), Diagnostics> {
        let stmts = self.ast.statements().to_vec();

        self.insert_structs(&stmts);
        self.insert_functions(&stmts);

        let _ = self.visit_statements(&stmts);

        if self.diagnostics.is_empty() {
            Ok((
                self.ast,
                self.symbols.replace(vec![]),
                Types::new(
                    self.types.replace(vec![]),
                    self.type_bindings
                        .iter()
                        .filter_map(|(id, t)| match t {
                            Ok(t) => Some((*id, *t)),
                            Err(_) => None,
                        })
                        .collect::<HashMap<Typed, TypeId>>(),
                ),
            ))
        } else {
            Err(self.diagnostics)
        }
    }

    fn insert_functions(&mut self, stmts: &[StmtId]) {
        for stmt in stmts {
            // we start by inserting all the functions we find, so that they are available from
            // everywhere in the current scope.
            if let StatementKind::LetFn(ident, params, ret_type, _) =
                self.ast.statement(*stmt).kind()
            {
                let ident_id = ident.id();
                let params_len = params.len();
                let ret_type = ret_type.clone();

                let parameter_types = params
                    .to_vec()
                    .iter()
                    .filter_map(|p| match self.resolve_type(p.ty().id(), p.span()) {
                        Ok(ty) => Some(ty),
                        Err(d) => {
                            self.diagnostics.push_all(d);
                            None
                        }
                    })
                    .collect::<Vec<TypeId>>();

                let ret_type = match ret_type {
                    None => Some(self.type_id(Type::Void)),
                    Some(t) => match self.resolve_type(t.id(), t.span()) {
                        Ok(t) => Some(t),
                        Err(d) => {
                            self.diagnostics.push_all(d);
                            None
                        }
                    },
                };

                if let Some(ret_type) = ret_type {
                    if parameter_types.len() == params_len {
                        self.insert_symbol(
                            ident_id,
                            SymbolKind::LetFn(*stmt, parameter_types, ret_type),
                            self.type_id(Type::Function),
                        );
                    }
                }
            }
        }
    }

    fn insert_structs(&mut self, stmts: &[StmtId]) {
        for stmt in stmts {
            // we start by inserting all the structs we find, so that they are available from
            // everywhere in the current scope.
            if let StatementKind::Struct(ident, _) = self.ast.statement(*stmt).kind() {
                self.insert_symbol(
                    ident.id(),
                    SymbolKind::Struct(*stmt),
                    self.type_id(Type::Void),
                )
            }
        }
    }

    fn insert_symbol(&mut self, ident: IdentId, kind: SymbolKind, ty: TypeId) {
        let id = SymbolId::from(self.symbols.borrow().len());
        self.symbols.borrow_mut().push(Symbol { id, kind, ty });
        self.scope_stack
            .last_mut()
            .expect("current scope exists")
            .symbols
            .entry(ident)
            .or_default()
            .push(id);
    }

    fn type_id(&self, kind: Type) -> TypeId {
        // todo use a map instead?
        let mut types = self.types.borrow_mut();

        for (i, t) in types.iter().enumerate() {
            if t == &kind {
                return TypeId::from(i);
            }
        }

        types.push(kind);

        TypeId::from(types.len() - 1)
    }

    fn type_str(&self, id: TypeId) -> String {
        self.types.borrow()[id.id()].to_string()
    }

    fn visit_expression(&mut self, expr: ExprId) -> Result<TypeId, ()> {
        let expr_id = expr;
        if let Some(ty) = self.type_bindings.get(&Typed::Expression(expr_id)) {
            return *ty;
        }

        let expr = self.ast.expression(expr);
        let ty = match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => self.visit_assignment(*ident_ref, *expr),
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(*cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => self.visit_literal(literal.kind().clone()),
            ExpressionKind::Binary(left, op, right) => self.visit_binary_operator(
                expr.id(),
                expr.span().clone(),
                *left,
                op.clone(),
                *right,
            ),
            ExpressionKind::Unary(op, operand) => {
                self.visit_unary_operator(expr.id(), expr.span().clone(), op.clone(), *operand)
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(*ident_ref, params.to_vec().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.visit_while(*cond, *expr),
            ExpressionKind::Block(stmts) => self.visit_block(&stmts.to_vec()),
            ExpressionKind::Dummy => {
                panic!()
            }
        };

        self.type_bindings.insert(Typed::Expression(expr_id), ty);
        ty
    }

    fn visit_assignment(&mut self, ident_ref: IdentRefId, expr: ExprId) -> Result<TypeId, ()> {
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

        let expr_type = self.visit_expression(expr)?;

        let expected_type = self
            // todo: to search for method, we need to extract the parameter types from the
            //  expr_type, it it corresponds to a function type. We don't have this
            //  information yet and this we cannot assign to a variable holding a function
            //  (yet).
            // todo: should IdentKind::Variable be renamed Binding to support the case where the
            //  target is a function?
            .resolve_ident_ref(ident_ref, IdentKind::Variable)
            .map(|s| self.symbols.borrow()[s.id()].ty)
            .ok_or(())?;

        if expr_type != expected_type {
            self.diagnostics.report_err(
                format!(
                    "Expected type {}, got {}",
                    self.type_str(expected_type),
                    self.type_str(expr_type),
                ),
                self.ast.expression(expr).span().clone(),
                (file!(), line!()),
            );
            return Err(());
        }

        Ok(expr_type)
    }

    fn visit_if(
        &mut self,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> Result<TypeId, ()> {
        let cond_type = self.visit_expression(cond)?;

        if cond_type != self.type_id(Type::Boolean) {
            self.diagnostics.report_err(
                format!(
                    "Expected type {}, got {}",
                    self.type_str(self.type_id(Type::Boolean)),
                    self.type_str(cond_type)
                ),
                self.ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        let true_branch_type = self.visit_expression(true_branch)?;
        let false_branch_type = false_branch
            .map(|e| self.visit_expression(e))
            .unwrap_or(Ok(self.type_id(Type::Void)))?;

        let none_type_id = self.type_id(Type::None);
        let void_type_id = self.type_id(Type::Void);

        if true_branch_type == none_type_id && false_branch_type == none_type_id {
            return Ok(none_type_id);
        }

        if true_branch_type == none_type_id {
            return Ok(false_branch_type);
        }

        if false_branch_type == none_type_id {
            return Ok(true_branch_type);
        }

        if true_branch_type == void_type_id || false_branch_type == void_type_id {
            // todo: option<t>
            return Ok(void_type_id);
        }

        if true_branch_type == false_branch_type {
            return Ok(true_branch_type);
        }

        let false_branch = self
            .ast
            .expression(false_branch.expect("false branch exists"));
        self.diagnostics.report_err(
            format!(
                "Expected type {}, got {}",
                self.type_str(true_branch_type),
                self.type_str(false_branch_type)
            ),
            false_branch.span().clone(),
            (file!(), line!()),
        );

        Err(())
    }

    fn visit_literal(&mut self, literal: LiteralKind) -> Result<TypeId, ()> {
        match literal {
            LiteralKind::Boolean(_) => Ok(self.type_id(Type::Boolean)),
            LiteralKind::Number(_) => Ok(self.type_id(Type::Number)),
            LiteralKind::Identifier(ident_ref) => {
                // todo things to check:
                //  - behaviour when target is let fn
                //  - behaviour when target is a native
                // todo resolve function ref, see comment in visit_assignment
                self.resolve_ident_ref(ident_ref, IdentKind::Variable)
                    .map(|s| self.symbols.borrow()[s.id()].ty)
                    .ok_or(())
            }
        }
    }

    fn visit_binary_operator(
        &mut self,
        expr: ExprId,
        expr_span: Span,
        left: ExprId,
        op: BinaryOperator,
        right: ExprId,
    ) -> Result<TypeId, ()> {
        if matches!(op.kind(), BinaryOperatorKind::Access) {
            return self.visit_access(left, right);
        }

        let left_type = self.visit_expression(left)?;
        let right_type = self.visit_expression(right)?;

        let ident_id = self.ast.identifier_id(op.kind().function_name());
        let symbol = match self.resolve_ident(
            ident_id,
            IdentKind::Callable(&[left_type, right_type]),
            op.span(),
        ) {
            Ok(s) => s,
            Err(d) => {
                self.diagnostics.push(d);
                return Err(());
            }
        };

        // here, we replace the `left op right` with `op_fn(left, right)` in the ast as a first
        // de-sugar action
        let ident_ref_id = self
            .ast
            .create_identifier_ref(Identifier::new(ident_id, op.span().clone()), symbol);
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, vec![left, right]),
            expr_span,
        );
        self.ast.replace_expression(expression);

        Ok(self.symbols.borrow()[symbol.id()].ty)
    }

    fn visit_access(&mut self, parent: ExprId, child: ExprId) -> Result<TypeId, ()> {
        if let Some(ty) = self.type_bindings.get(&Typed::Expression(child)) {
            return *ty;
        }

        let parent_type = self.visit_expression(parent)?;
        let parent_type = &self.types.borrow()[parent_type.id()];

        // todo if we have a dedicated enum variant for access, we can simplify this by putting the IdentId directly
        //  in it
        let child_ident_ref =
            if let ExpressionKind::Literal(lit) = self.ast.expression(child).kind() {
                if let LiteralKind::Identifier(ident_ref) = lit.kind() {
                    self.ast.identifier_ref(*ident_ref)
                } else {
                    panic!("expected identifier")
                }
            } else {
                panic!("expected literal")
            };

        let field_type = match parent_type {
            Type::Struct(_, fields) => fields
                .iter()
                .find(|(name, _)| name == &child_ident_ref.ident().id())
                .map(|(_, t)| *t),
            _ => None,
        };

        match field_type {
            Some(t) => {
                self.type_bindings.insert(Typed::Expression(child), Ok(t));
                Ok(t)
            }
            None => {
                self.diagnostics.report_err(
                    format!(
                        "No field '{}' found",
                        self.ast.identifier(child_ident_ref.ident().id()),
                    ),
                    self.ast.expression(parent).span().clone(),
                    (file!(), line!()),
                );
                Err(())
            }
        }
    }

    fn visit_unary_operator(
        &mut self,
        expr: ExprId,
        expr_span: Span,
        op: UnaryOperator,
        operand: ExprId,
    ) -> Result<TypeId, ()> {
        let operand_type = self.visit_expression(operand)?;

        let ident_id = self.ast.identifier_id(op.kind().function_name());
        let symbol =
            match self.resolve_ident(ident_id, IdentKind::Callable(&[operand_type]), op.span()) {
                Ok(s) => s,
                Err(d) => {
                    self.diagnostics.push(d);
                    return Err(());
                }
            };

        // here, we replace the `op operand` with `op_fn(operand)` in the ast as a first
        // de-sugar action
        let ident_ref_id = self
            .ast
            .create_identifier_ref(Identifier::new(ident_id, op.span().clone()), symbol);
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, vec![operand]),
            expr_span,
        );
        self.ast.replace_expression(expression);

        Ok(self.symbols.borrow()[symbol.id()].ty)
    }

    fn visit_function_call(
        &mut self,
        ident_ref: IdentRefId,
        params: &[ExprId],
    ) -> Result<TypeId, ()> {
        let param_types = params
            .iter()
            .filter_map(|e| self.visit_expression(*e).ok())
            .collect::<Vec<TypeId>>();

        if param_types.len() != params.len() {
            return Err(());
        }

        self.resolve_ident_ref(ident_ref, IdentKind::Callable(&param_types))
            .map(|s| match &self.symbols.borrow()[s.id()].kind {
                SymbolKind::LetFn(_, _, ret_type) => Ok(*ret_type),
                SymbolKind::NativeFn(_, _, ret_type, _) => Ok(*ret_type),
                _ => panic!("the resolved symbol was not a function"),
            })
            .ok_or(())?
    }

    fn visit_while(&mut self, cond: ExprId, expr: ExprId) -> Result<TypeId, ()> {
        let cond_type = self.visit_expression(cond)?;

        if cond_type != self.type_id(Type::Boolean) {
            self.diagnostics.report_err(
                format!(
                    "Expected type {}, got {}",
                    self.type_str(self.type_id(Type::Boolean)),
                    self.type_str(cond_type)
                ),
                self.ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        self.visit_expression(expr)
    }

    fn visit_block(&mut self, stmts: &[StmtId]) -> Result<TypeId, ()> {
        self.push_scope();

        self.insert_functions(stmts);
        let ret_type = self.visit_statements(stmts);

        self.pop_scope();

        ret_type
    }

    fn visit_statements(&mut self, stmts: &[StmtId]) -> Result<TypeId, ()> {
        let void_type_id = self.type_id(Type::Void);
        let none_type_id = self.type_id(Type::None);

        let mut ret_type = Ok(void_type_id);

        for stmt in stmts.iter() {
            let stmt_type = match self.ast.statement(*stmt).kind() {
                StatementKind::Expression(expr) => self.visit_expression(*expr),
                StatementKind::Let(ident, expr) => {
                    self.visit_let(*stmt, ident.id(), *expr);
                    Ok(void_type_id)
                }
                StatementKind::Ret(expr) => {
                    let _ = self.visit_expression(*expr);
                    Ok(none_type_id)
                }
                StatementKind::LetFn(_ident, params, ret_type, expr) => {
                    self.visit_function(*stmt, &params.to_vec(), ret_type.clone().as_ref(), *expr);
                    Ok(void_type_id)
                }
                StatementKind::Struct(_ident, fields) => {
                    self.visit_struct(*stmt, &fields.to_vec());
                    Ok(void_type_id)
                }
            };

            match ret_type {
                Ok(t) if t == none_type_id => {
                    // we keep the type of the expression only if we did not already see a `ret`
                }
                _ => ret_type = stmt_type,
            }
        }

        ret_type
    }

    fn visit_let(&mut self, stmt: StmtId, ident: IdentId, expr: ExprId) {
        match self.visit_expression(expr) {
            Ok(t) if t != self.type_id(Type::None) => {
                self.insert_symbol(ident, SymbolKind::Let(stmt), t);
            }
            Ok(t) => {
                let expr = self.ast.expression(expr);
                self.diagnostics.report_err(
                    format!("Expected some type, got {}", self.type_str(t)),
                    expr.span().clone(),
                    (file!(), line!()),
                );
            }
            Err(_) => {}
        }
    }

    fn visit_function(
        &mut self,
        stmt: StmtId,
        params: &[Parameter],
        ret_type: Option<&Identifier>,
        expr: ExprId,
    ) {
        self.push_scope();

        let ret_type = ret_type
            .map(|t| match self.resolve_type(t.id(), t.span()) {
                Ok(t) => t,
                Err(d) => {
                    self.diagnostics.push_all(d);
                    self.type_id(Type::Void)
                }
            })
            .unwrap_or(self.type_id(Type::Void));

        for (index, parameter) in params.iter().enumerate() {
            let ty = match self.resolve_type(parameter.ty().id(), parameter.ty().span()) {
                Ok(ty) => {
                    self.type_bindings
                        .insert(Typed::Parameter(stmt, index), Ok(ty));
                    ty
                }
                Err(d) => {
                    self.type_bindings
                        .insert(Typed::Parameter(stmt, index), Err(()));
                    self.diagnostics.push_all(d);
                    self.type_id(Type::Void)
                }
            };

            self.insert_symbol(
                parameter.identifier().id(),
                SymbolKind::Parameter(stmt, index),
                ty,
            )
        }

        let _ = self.visit_expression(expr);

        let exit_points = ExitPoints::new(&self.ast).exit_points(expr);
        if exit_points.is_empty() {
            if ret_type != self.type_id(Type::Void) {
                let stmt = self.ast.statement(stmt);
                self.diagnostics.report_err(
                    format!("Expected type {}, got void", self.type_str(ret_type)),
                    stmt.span().clone(),
                    (file!(), line!()),
                );
            }
        } else {
            for exit_point in exit_points {
                let (expr, explicit) = match exit_point {
                    ExitPoint::Explicit(e) => (e, true),
                    ExitPoint::Implicit(e) => (e, false),
                };
                match self.visit_expression(expr) {
                    Ok(expr_type) if expr_type == self.type_id(Type::None) => {
                        panic!("functions must not return {}", self.type_str(expr_type));
                    }
                    Ok(expr_type) => {
                        if expr_type != ret_type
                            && (ret_type != self.type_id(Type::Void) || explicit)
                        {
                            let expr = self.ast.expression(expr);
                            self.diagnostics.report_err(
                                format!(
                                    "Expected type {}, got {}",
                                    self.type_str(ret_type),
                                    self.type_str(expr_type),
                                ),
                                expr.span().clone(),
                                (file!(), line!()),
                            );
                        }
                    }
                    Err(_) => {}
                }
            }
        }

        self.pop_scope();
    }

    fn visit_struct(&mut self, stmt: StmtId, fields: &[Field]) {
        let mut used_identifiers = Vec::with_capacity(fields.len());

        for (index, field) in fields.iter().enumerate() {
            if used_identifiers.contains(&field.identifier().id()) {
                self.diagnostics.report_err(
                    format!(
                        "Field '{}' is already defined",
                        self.ast.identifier(field.identifier().id())
                    ),
                    field.identifier().span().clone(),
                    (file!(), line!()),
                );
            } else {
                used_identifiers.push(field.identifier().id());
            }

            match self.resolve_type(field.ty().id(), field.ty().span()) {
                Ok(ty) => {
                    self.type_bindings.insert(Typed::Field(stmt, index), Ok(ty));
                }
                Err(d) => self.diagnostics.push_all(d),
            }
        }
    }

    fn resolve_type(&self, ident: IdentId, span: &Span) -> Result<TypeId, Vec<Diagnostic>> {
        self.resolve_ident(ident, IdentKind::Type, span)
            .map_err(|d| vec![d])
            .and_then(|s| match self.symbols.borrow()[s.id()].kind() {
                SymbolKind::Struct(stmt) => {
                    let fields = match self.ast.statement(*stmt).kind() {
                        StatementKind::Struct(_, fields) => fields,
                        _ => panic!("expected struct"),
                    };

                    let mut resolved_fields = Vec::with_capacity(fields.len());
                    let mut diagnostics = Vec::new();
                    for field in fields {
                        match self.resolve_type(field.ty().id(), field.ty().span()) {
                            Ok(ty) => resolved_fields.push((field.identifier().id(), ty)),
                            Err(mut d) => {
                                diagnostics.append(&mut d);
                            }
                        }
                    }

                    if !diagnostics.is_empty() {
                        return Err(diagnostics);
                    }

                    Ok(self.type_id(Type::Struct(*stmt, resolved_fields)))
                }
                SymbolKind::NativeType(native) => Ok(self.type_id(native.ty().clone())),
                _ => panic!("the resolved symbol was not a type"),
            })
    }

    fn resolve_ident_ref(
        &mut self,
        ident_ref: IdentRefId,
        ident_kind: IdentKind,
    ) -> Option<SymbolId> {
        let ident_ref = self.ast.identifier_ref(ident_ref);

        if let Some(symbol) = ident_ref.symbol_id() {
            return Some(symbol);
        }

        let ident_ref = ident_ref.clone();
        match self.resolve_ident(ident_ref.ident().id(), ident_kind, ident_ref.ident().span()) {
            Err(d) => {
                self.diagnostics.push(d);
                None
            }
            Ok(s) => {
                let mut ident_ref = ident_ref;
                ident_ref.set_symbol_id(s);
                self.ast.replace_identifier_ref(ident_ref);
                Some(s)
            }
        }
    }

    fn resolve_ident(
        &self,
        ident: IdentId,
        ident_kind: IdentKind,
        span: &Span,
    ) -> Result<SymbolId, Diagnostic> {
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&ident, ident_kind))
        {
            Some(s) => Ok(s),
            None => {
                // todo nice to have: propose known alternatives
                match ident_kind {
                    IdentKind::Variable => Err(Diagnostic::error(
                        format!("No variable '{}' found", self.ast.identifier(ident)),
                        span.clone(),
                        (file!(), line!()),
                    )),
                    IdentKind::Callable(param_types) => {
                        // todo nice to have: when it comes from an operator, state it in the error
                        //   message
                        Err(Diagnostic::error(
                            format!(
                                "No function '{}' found for parameters of types ({})",
                                self.ast.identifier(ident),
                                param_types
                                    .iter()
                                    .map(|t| self.type_str(*t))
                                    .collect::<Vec<String>>()
                                    .join(", ")
                            ),
                            span.clone(),
                            (file!(), line!()),
                        ))
                    }
                    IdentKind::Type => Err(Diagnostic::error(
                        format!("No type '{}' found", self.ast.identifier(ident)),
                        span.clone(),
                        (file!(), line!()),
                    )),
                }
            }
        }
    }

    fn push_scope(&mut self) {
        self.scope_stack.push(Scope::new(self.symbols.clone()));
    }

    fn pop_scope(&mut self) {
        self.scope_stack.pop();
    }
}

#[derive(Clone, Copy)]
enum IdentKind<'a> {
    Variable,
    Callable(&'a [TypeId]),
    Type,
}

struct Scope {
    all_symbols: Rc<RefCell<Vec<Symbol>>>,
    symbols: HashMap<IdentId, Vec<SymbolId>>,
}

impl Scope {
    fn new(all_symbols: Rc<RefCell<Vec<Symbol>>>) -> Self {
        Self {
            all_symbols,
            symbols: Default::default(),
        }
    }

    fn find(&self, ident: &IdentId, ident_kind: IdentKind) -> Option<SymbolId> {
        self.symbols.get(ident).and_then(|symbols| {
            symbols
                .iter()
                .rev()
                .find(
                    |s| match (ident_kind, &self.all_symbols.borrow()[s.id()].kind) {
                        (IdentKind::Variable, SymbolKind::Let(_)) => true,
                        (IdentKind::Variable, SymbolKind::Parameter(_, _)) => true,
                        (IdentKind::Callable(t1), SymbolKind::LetFn(_, ref t2, _)) => {
                            t1 == t2.as_slice()
                        }
                        (
                            IdentKind::Callable(param_types),
                            SymbolKind::NativeFn(_, params, _, _),
                        ) => param_types == params.as_slice(),
                        (IdentKind::Type, SymbolKind::Struct(_)) => true,
                        (IdentKind::Type, SymbolKind::NativeType(_)) => true,
                        (_, _) => false,
                    },
                )
                .copied()
        })
    }
}

#[derive(Debug)]
pub struct Symbol {
    // todo remove if not useful
    id: SymbolId,
    kind: SymbolKind,
    ty: TypeId,
}

impl Symbol {
    pub fn kind(&self) -> &SymbolKind {
        &self.kind
    }
}

#[derive(Debug)]
pub enum SymbolKind {
    Let(StmtId),
    // todo could have the body here too (i.e. Vec<StmtId>)
    LetFn(StmtId, Vec<TypeId>, TypeId),
    // todo could have IdentId, TypeId and usize
    Parameter(StmtId, usize),
    // todo could have the Vec<...>
    Struct(StmtId),
    NativeFn(IdentId, Vec<TypeId>, TypeId, fn(Vec<Value>) -> Value),
    NativeType(NativeType),
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub enum Type {
    Boolean,
    // fixme this is not enough
    Function,
    Number,
    Void,
    Struct(StmtId, Vec<(IdentId, TypeId)>),
    /// This value is used when the statement/expression does not return any value. This is the
    /// case of `ret` for instance.
    None,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "{}", natives::TYPE_BOOLEAN),
            Type::Function => write!(f, "function TODO"),
            Type::Number => write!(f, "{}", natives::TYPE_NUMBER),
            Type::Struct(_, fields) => write!(f, "struct/{}", fields.len()),
            Type::Void => write!(f, "{}", natives::TYPE_VOID),
            Type::None => write!(f, "no type"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Typed {
    Expression(ExprId),
    Parameter(StmtId, usize),
    Field(StmtId, usize),
}

#[derive(Debug)]
pub struct Types {
    types: Vec<Type>,
    bindings: HashMap<Typed, TypeId>,
}

impl Types {
    fn new(types: Vec<Type>, bindings: HashMap<Typed, TypeId>) -> Self {
        Self { types, bindings }
    }

    pub fn empty() -> Self {
        Self::new(Default::default(), Default::default())
    }

    pub fn expression_type(&self, expr_id: ExprId) -> Option<TypeId> {
        self.bindings.get(&Typed::Expression(expr_id)).copied()
    }

    pub fn parameter_type(&self, stmt_id: StmtId, index: usize) -> Option<TypeId> {
        self.bindings
            .get(&Typed::Parameter(stmt_id, index))
            .copied()
    }

    pub fn field_type(&self, stmt_id: StmtId, index: usize) -> Option<TypeId> {
        self.bindings.get(&Typed::Field(stmt_id, index)).copied()
    }

    pub fn get(&self, id: TypeId) -> Option<&Type> {
        self.types.get(id.id())
    }

    pub fn iter(&self) -> Iter {
        Iter {
            types: &self.types,
            index: 0,
        }
    }
}

pub struct Iter<'a> {
    types: &'a Vec<Type>,
    index: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a Type;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index == self.types.len() {
            None
        } else {
            self.index += 1;
            Some(&self.types[self.index - 1])
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::dot::Dot;
    use crate::error::Level;
    use crate::lexer::{Lexer, Span};
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

    #[test]
    fn resolve_ref_to_parameter() {
        let (ast, diagnostics) =
            Parser::new(Lexer::new("let x(n: number): number = { n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols, types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("no error expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols, &types).serialize());
    }

    #[test]
    fn resolve_ref_to_let() {
        let (ast, diagnostics) =
            Parser::new(Lexer::new("let x(): number = { let n = 0; n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols, types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols, &types).serialize());
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let (ast, diagnostics) = Parser::new(Lexer::new("let x() = { } x();")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols, types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols, &types).serialize());
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            "let x(n: number): number = { while true { ret n; } }",
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols, types) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols, &types).serialize());
    }

    #[test]
    fn resolve_missing_def() {
        let (ast, diagnostics) = Parser::new(Lexer::new("let x() = { n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let actual_diagnostics = Resolver::new(ast, Natives::default())
            .resolve()
            .expect_err("err expected");

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
        let (ast, diagnostics) = Parser::new(Lexer::new("let x = true; let x = 1; x + 1;")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols, types) = Resolver::new(ast, Natives::default()).resolve().unwrap();

        assert_snapshot!(
            "rebinding-xml",
            XmlWriter::new(&ast, &symbols, &types).serialize()
        );
        assert_snapshot!(
            "rebinding-dot",
            Dot::new(&ast, &symbols, &types).serialize()
        );
    }

    macro_rules! test_type_error {
        ($name:ident, $src:expr, $error:expr, $span:expr) => {
            #[test]
            fn $name() {
                let (ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{}", diagnostics);

                let actual_diagnostics = Resolver::new(ast, Natives::default())
                    .resolve()
                    .expect_err("err expected");

                let actual_diagnostics = actual_diagnostics
                    .iter()
                    .map(|d| (d.message(), d.span().clone(), d.level()))
                    .collect::<Vec<(&str, Span, Level)>>();

                let expected_diagnostics = vec![($error, $span, Level::Error)];

                assert_eq!(actual_diagnostics, expected_diagnostics);
            }
        };
    }

    macro_rules! test_type_ok {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let (ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{}", diagnostics);

                let _ = Resolver::new(ast, Natives::default())
                    .resolve()
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
    test_type_error!(
        function_void_cannot_return_number,
        "let f() = { ret 1; }",
        "Expected type void, got number",
        Span::new(1, 17, 16, 1)
    );
    test_type_error!(
        function_invalid_return_type,
        "let f(): unknown = { }",
        "No type 'unknown' found",
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
    test_type_error!(
        function_parameter_incorrect_type,
        "let f(n: number) = { let a = n + true; }",
        "No function 'add' found for parameters of types (number, boolean)",
        Span::new(1, 32, 31, 1)
    );
    test_type_error!(
        function_parameter_incorrect_type_when_called,
        "struct S {} let f(t: S) = { } f(1);",
        "No function 'f' found for parameters of types (number)",
        Span::new(1, 31, 30, 1)
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
    test_type_error!(
        invalid_field_access,
        "let n = 10; n.field;",
        "No field 'field' found",
        Span::new(1, 13, 12, 1)
    );
    test_type_error!(
        invalid_field_type,
        "struct Point { x: number, y: number } let f(p: Point) = { if p.x { } }",
        "Expected type boolean, got number",
        Span::new(1, 62, 61, 3)
    );
    // fixme un-comment the following test
    // test_type_ok!(
    //     assign_from_native,
    //     "let n = add;"
    // );
    test_type_error!(
        struct_use_same_field_identifier_twice,
        "struct Point { x: number, y: number, x: boolean }",
        "Field 'x' is already defined",
        Span::new(1, 38, 37, 1)
    );
    test_type_ok!(
        struct_use,
        "struct Point { x: number, y: number } let dist(from: Point, to: Point) = { }"
    );
    test_type_ok!(
        struct_field_access,
        "struct Point { x: number, y: number } let f(p: Point) = { p.x + 1; }"
    );
}
