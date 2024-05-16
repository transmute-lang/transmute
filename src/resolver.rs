use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::{Identifier, IdentifierRef, ResolvedSymbol};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId};
use crate::ast::literal::LiteralKind;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::{Parameter, StatementKind};
use crate::ast::{Ast, WithoutImplicitRet};
use crate::error::Diagnostics;
use crate::exit_points::{ExitPoint, ExitPoints};
use crate::lexer::Span;
use crate::natives::{Native, Natives};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

pub struct Resolver {
    resolved_identifier_refs: Vec<Option<IdentifierRef<ResolvedSymbol>>>,
    expression: Vec<Expression>,
    symbols: Rc<RefCell<Vec<Symbol>>>,
    expression_types: Vec<Option<Result<Type, ()>>>,
    diagnostics: Diagnostics,
    scope_stack: Vec<Scope>,
}

pub struct Resolution {
    pub identifier_refs: Vec<IdentifierRef<ResolvedSymbol>>,
    pub symbols: Vec<Symbol>,
    pub expression_types: Vec<Type>,
    pub expressions: Vec<Expression>,
}

impl Resolver {
    pub fn new() -> Self {
        Self {
            resolved_identifier_refs: Vec::new(),
            expression: Vec::new(),
            symbols: Rc::new(RefCell::new(Vec::<Symbol>::new())),
            expression_types: Vec::new(),
            diagnostics: Default::default(),
            scope_stack: Vec::new(),
        }
    }

    pub fn resolve(
        mut self,
        ast: &Ast<WithoutImplicitRet>,
        natives: Natives,
    ) -> Result<Resolution, Diagnostics> {
        // let ast = ast.merge(Into::<Ast<WithoutImplicitRet>>::into(&natives));

        self.resolved_identifier_refs
            .resize(ast.identifier_ref_count(), None);
        self.expression_types.resize(ast.expressions_count(), None);
        self.scope_stack.push(Scope::new(self.symbols.clone()));

        for native in natives.into_iter() {
            let ident = ast.identifier_id(native.name());
            self.insert_symbol(ast, ident, SymbolKind::Native(native), Type::Function);
        }

        let stmts = ast.statements().to_vec();

        self.insert_functions(ast, &stmts);

        let _ = self.visit_statements(ast, &stmts);

        if self.diagnostics.is_empty() {
            Ok(Resolution {
                identifier_refs: self
                    .resolved_identifier_refs
                    .into_iter()
                    .map(|id_ref| id_ref.expect("identifier ref is resolved"))
                    .collect::<Vec<IdentifierRef<ResolvedSymbol>>>(),
                symbols: self.symbols.replace(vec![]),
                expression_types: self
                    .expression_types
                    .into_iter()
                    .map(|ty| ty.expect("type is resolved"))
                    .map(|ty| ty.expect("type is resolved successfully"))
                    .collect::<Vec<Type>>(),
                expressions: self.expression,
            })
        } else {
            Err(self.diagnostics)
        }
    }

    fn insert_functions(&mut self, ast: &Ast<WithoutImplicitRet>, stmts: &[StmtId]) {
        for stmt in stmts {
            // we start by inserting all the functions we find, so that they are available from
            // everywhere in the current scope.
            if let StatementKind::LetFn(ident, params, ret_type, _) = ast.statement(*stmt).kind() {
                let parameter_types = params
                    .iter()
                    .filter_map(|p| match Type::try_from(ast.identifier(p.ty().id())) {
                        Ok(t) => Some(t),
                        Err(e) => {
                            self.diagnostics.report_err(
                                e,
                                p.ty().span().clone(),
                                (file!(), line!()),
                            );
                            None
                        }
                    })
                    .collect::<Vec<Type>>();

                let ret_type = ret_type
                    .as_ref()
                    .map(|t| match Type::try_from(ast.identifier(t.id())) {
                        Ok(t) => Some(t),
                        Err(e) => {
                            self.diagnostics
                                .report_err(e, t.span().clone(), (file!(), line!()));
                            None
                        }
                    })
                    .unwrap_or(Some(Type::Void));

                if let Some(ret_type) = ret_type {
                    if parameter_types.len() == params.len() {
                        self.insert_symbol(
                            ast,
                            ident.id(),
                            SymbolKind::LetFn(*stmt, parameter_types, ret_type),
                            Type::Function,
                        );
                    }
                }
            }
        }
    }

    fn insert_symbol(
        &mut self,
        _ast: &Ast<WithoutImplicitRet>,
        ident: IdentId,
        kind: SymbolKind,
        ty: Type,
    ) {
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

    fn visit_expression(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        expr: ExprId,
    ) -> Result<Type, ()> {
        let expr_id = expr.id();
        if let Some(ty) = self.expression_types[expr_id] {
            return ty;
        }

        let expr = ast.expression(expr);
        let ty = match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                self.visit_assignment(ast, *ident_ref, *expr)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(ast, *cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => self.visit_literal(ast, literal.kind().clone()),
            ExpressionKind::Binary(left, op, right) => self.visit_binary_operator(
                ast,
                expr.id(),
                expr.span().clone(),
                *left,
                op.clone(),
                *right,
            ),
            ExpressionKind::Unary(op, operand) => {
                self.visit_unary_operator(ast, expr.id(), expr.span().clone(), op.clone(), *operand)
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(ast, *ident_ref, params.to_vec().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.visit_while(ast, *cond, *expr),
            ExpressionKind::Block(stmts) => self.visit_block(ast, &stmts.to_vec()),
            ExpressionKind::Dummy => {
                panic!()
            }
        };

        self.expression_types[expr_id] = Some(ty);
        ty
    }

    fn visit_assignment(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        ident_ref: IdentRefId,
        expr: ExprId,
    ) -> Result<Type, ()> {
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

        let expr_type = self.visit_expression(ast, expr)?;

        let expected_type = self
            // todo: to search for method, we need to extract the parameter types from the
            //  expr_type, it it corresponds to a function type. We don't have this
            //  information yet and this we cannot assign to a variable holding a function
            //  (yet).
            .resolve_ident_ref(ast, ident_ref, None)
            .map(|s| self.symbols.borrow()[s.id()].ty)
            .ok_or(())?;

        if expr_type != expected_type {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", expected_type, expr_type),
                ast.expression(expr).span().clone(),
                (file!(), line!()),
            );
            return Err(());
        }

        Ok(expr_type)
    }

    fn visit_if(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> Result<Type, ()> {
        let cond_type = self.visit_expression(ast, cond)?;

        if cond_type != Type::Boolean {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", Type::Boolean, cond_type),
                ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        let true_branch_type = self.visit_expression(ast, true_branch)?;
        let false_branch_type = false_branch
            .map(|e| self.visit_expression(ast, e))
            .unwrap_or(Ok(Type::Void))?;

        match (true_branch_type, false_branch_type) {
            (Type::None, Type::None) => Ok(Type::None),
            (Type::None, t) | (t, Type::None) => Ok(t),
            (_, Type::Void) | (Type::Void, _) => {
                // todo: option<t>
                Ok(Type::Void)
            }
            (tt, ft) if tt == ft => Ok(tt),
            (tt, ft) => {
                let false_branch = ast.expression(false_branch.expect("false branch exists"));
                self.diagnostics.report_err(
                    format!("Expected type {tt}, got {ft}"),
                    false_branch.span().clone(),
                    (file!(), line!()),
                );
                Err(())
            }
        }
    }

    fn visit_literal(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        literal: LiteralKind,
    ) -> Result<Type, ()> {
        match literal {
            LiteralKind::Boolean(_) => Ok(Type::Boolean),
            LiteralKind::Number(_) => Ok(Type::Number),
            LiteralKind::Identifier(ident_ref) => {
                // todo things to check:
                //  - behaviour when target is let fn
                //  - behaviour when target is a native
                // todo resolve function ref, see comment in resolve_assignment
                self.resolve_ident_ref(ast, ident_ref, None)
                    .map(|s| self.symbols.borrow()[s.id()].ty)
                    .ok_or(())
            }
        }
    }

    fn visit_binary_operator(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        expr: ExprId,
        expr_span: Span,
        left: ExprId,
        op: BinaryOperator,
        right: ExprId,
    ) -> Result<Type, ()> {
        let left_type = self.visit_expression(ast, left)?;
        let right_type = self.visit_expression(ast, right)?;

        let ident_id = ast.identifier_id(op.kind().function_name());
        let symbol = self
            .resolve_ident(ast, ident_id, Some(&[left_type, right_type]), op.span())
            .ok_or(())?;

        let ident_ref_id =
            self.create_identifier_ref(ast, Identifier::new(ident_id, op.span().clone()), symbol);
        let parameters = vec![left, right];
        let ret_type = self.visit_function_call(ast, ident_ref_id, &parameters)?;

        // here, we replace the `left op right` with `op_fn(left, right)` in the ast as a de-sugar
        // action
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, parameters),
            expr_span,
        );
        self.expression.push(expression);

        Ok(ret_type)
    }

    fn create_identifier_ref(
        &mut self,
        _ast: &Ast<WithoutImplicitRet>,
        identifier: Identifier,
        symbol: SymbolId,
    ) -> IdentRefId {
        let id = IdentRefId::from(self.resolved_identifier_refs.len());
        self.resolved_identifier_refs
            .push(Some(IdentifierRef::new_resolved(id, identifier, symbol)));
        id
    }

    fn visit_unary_operator(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        expr: ExprId,
        expr_span: Span,
        op: UnaryOperator,
        operand: ExprId,
    ) -> Result<Type, ()> {
        let operand_type = self.visit_expression(ast, operand)?;

        let ident_id = ast.identifier_id(op.kind().function_name());
        let symbol = self
            .resolve_ident(ast, ident_id, Some(&[operand_type]), op.span())
            .ok_or(())?;

        let ident_ref_id =
            self.create_identifier_ref(ast, Identifier::new(ident_id, op.span().clone()), symbol);
        let parameter = vec![operand];
        let ret_type = self.visit_function_call(ast, ident_ref_id, &parameter)?;

        // here, we replace the `op operand` with `op_fn(operand)` in the ast as a de-sugar action
        let expression = Expression::new(
            expr,
            ExpressionKind::FunctionCall(ident_ref_id, parameter),
            expr_span,
        );
        self.expression.push(expression);

        Ok(ret_type)
    }

    fn visit_function_call(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        ident_ref: IdentRefId,
        params: &[ExprId],
    ) -> Result<Type, ()> {
        let param_types = params
            .iter()
            .filter_map(|e| self.visit_expression(ast, *e).ok())
            .collect::<Vec<Type>>();

        if param_types.len() != params.len() {
            // todo better error
            return Err(());
        }

        self.resolve_ident_ref(ast, ident_ref, Some(&param_types))
            .map(|s| match &self.symbols.borrow()[s.id()].kind {
                SymbolKind::LetFn(_, _, ret_type) => Ok(*ret_type),
                SymbolKind::Native(native) => Ok(native.return_type()),
                SymbolKind::Let(_) | SymbolKind::Parameter(_, _) => {
                    panic!("the resolved symbol was not a function")
                }
            })
            .ok_or(())?
    }

    fn visit_while(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        cond: ExprId,
        expr: ExprId,
    ) -> Result<Type, ()> {
        let cond_type = self.visit_expression(ast, cond)?;

        if cond_type != Type::Boolean {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", Type::Boolean, cond_type),
                ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        self.visit_expression(ast, expr)
    }

    fn visit_block(&mut self, ast: &Ast<WithoutImplicitRet>, stmts: &[StmtId]) -> Result<Type, ()> {
        self.push_scope();

        self.insert_functions(ast, stmts);
        let ty = self.visit_statements(ast, stmts);

        self.pop_scope();

        ty
    }

    fn visit_statements(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        stmts: &[StmtId],
    ) -> Result<Type, ()> {
        let mut ret_type = Ok(Type::Void);

        for stmt in stmts.iter() {
            let stmt_type = match ast.statement(*stmt).kind() {
                StatementKind::Expression(expr) => self.visit_expression(ast, *expr),
                StatementKind::Let(ident, expr) => {
                    self.visit_let(ast, *stmt, ident.id(), *expr);
                    Ok(Type::Void)
                }
                StatementKind::Ret(expr, _) => {
                    let _ = self.visit_expression(ast, *expr);
                    Ok(Type::None)
                }
                StatementKind::LetFn(_ident, params, ret_type, expr) => {
                    self.visit_function(
                        ast,
                        *stmt,
                        &params.to_vec(),
                        ret_type.clone().as_ref(),
                        *expr,
                    );
                    Ok(Type::Void)
                }
            };

            match ret_type {
                Ok(Type::None) => {
                    // we keep the type of the expression only if we did not already see a `ret`
                }
                _ => ret_type = stmt_type,
            }
        }

        ret_type
    }

    fn visit_let(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        stmt: StmtId,
        ident: IdentId,
        expr: ExprId,
    ) {
        match self.visit_expression(ast, expr) {
            Ok(Type::None) => {
                let expr = ast.expression(expr);
                self.diagnostics.report_err(
                    format!("Expected some type, got {}", Type::None),
                    expr.span().clone(),
                    (file!(), line!()),
                );
            }
            Ok(t) => {
                self.insert_symbol(ast, ident, SymbolKind::Let(stmt), t);
            }
            Err(_) => {}
        }
    }

    fn visit_function(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        stmt: StmtId,
        params: &[Parameter],
        ret_type: Option<&Identifier>,
        expr: ExprId,
    ) {
        self.push_scope();

        let ret_type = ret_type
            .map(|t| match Type::try_from(ast.identifier(t.id())) {
                Ok(t) => t,
                Err(_) => {
                    // no need to report error here, it was already reported in insert_functions
                    Type::Void
                }
            })
            .unwrap_or(Type::Void);

        for (index, parameter) in params.iter().enumerate() {
            let ty = match Type::try_from(ast.identifier(parameter.ty().id())) {
                Ok(ty) => ty,
                Err(_) => {
                    // no need to report error here, it was already reported in insert_functions
                    Type::Void
                }
            };

            self.insert_symbol(
                ast,
                parameter.identifier().id(),
                SymbolKind::Parameter(stmt, index),
                ty,
            )
        }

        let _ = self.visit_expression(ast, expr);

        let exit_points = ExitPoints::new(ast).exit_points(expr);
        if exit_points.is_empty() {
            if ret_type != Type::Void {
                let stmt = ast.statement(stmt);
                self.diagnostics.report_err(
                    format!("Expected type {ret_type}, got void"),
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
                match self.visit_expression(ast, expr) {
                    Ok(Type::None) => panic!("functions must not return {}", Type::None),
                    Ok(expr_type) => {
                        if expr_type != ret_type && (ret_type != Type::Void || explicit) {
                            let expr = ast.expression(expr);
                            self.diagnostics.report_err(
                                format!("Expected type {ret_type}, got {expr_type}"),
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

    fn resolve_ident_ref(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        ident_ref: IdentRefId,
        param_types: Option<&[Type]>,
    ) -> Option<SymbolId> {
        if let Some(ident_ref) = &self.resolved_identifier_refs[ident_ref.id()] {
            return Some(ident_ref.symbol_id());
        }

        let ident_ref = ast.identifier_ref(ident_ref);

        let ident_id = ident_ref.ident_id();
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&ident_id, param_types))
        {
            Some(s) => {
                self.resolved_identifier_refs[ident_ref.id().id()] = Some(ident_ref.resolved(s));
                Some(s)
            }
            None => {
                // todo nice to have: propose known alternatives
                if let Some(param_types) = param_types {
                    self.diagnostics.report_err(
                        format!(
                            "No function '{}' found for parameters of types ({})",
                            ast.identifier(ident_id),
                            param_types
                                .iter()
                                .map(Type::to_string)
                                .collect::<Vec<String>>()
                                .join(", ")
                        ),
                        ident_ref.ident().span().clone(),
                        (file!(), line!()),
                    );
                } else {
                    self.diagnostics.report_err(
                        format!("No variable '{}' found", ast.identifier(ident_id)),
                        ident_ref.ident().span().clone(),
                        (file!(), line!()),
                    );
                }
                None
            }
        }
    }

    fn resolve_ident(
        &mut self,
        ast: &Ast<WithoutImplicitRet>,
        ident: IdentId,
        param_types: Option<&[Type]>,
        span: &Span,
    ) -> Option<SymbolId> {
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&ident, param_types))
        {
            Some(s) => Some(s),
            None => {
                // todo nice to have: propose known alternatives
                if let Some(param_types) = param_types {
                    // todo nice to have: when it comes from an operator, state it in the error
                    //   message (always when we're here, actually...)
                    self.diagnostics.report_err(
                        format!(
                            "No function '{}' found for parameters of types ({})",
                            ast.identifier(ident),
                            param_types
                                .iter()
                                .map(Type::to_string)
                                .collect::<Vec<String>>()
                                .join(", ")
                        ),
                        span.clone(),
                        (file!(), line!()),
                    );
                } else {
                    self.diagnostics.report_err(
                        format!("No variable '{}' found", ast.identifier(ident)),
                        span.clone(),
                        (file!(), line!()),
                    );
                }
                None
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

    fn find(&self, ident: &IdentId, param_types: Option<&[Type]>) -> Option<SymbolId> {
        self.symbols.get(ident).and_then(|symbols| {
            symbols
                .iter()
                .rev()
                .find(|s| {
                    let symbol = &self.all_symbols.borrow()[s.id()];
                    match param_types {
                        None => match symbol.kind {
                            SymbolKind::LetFn(_, _, _) | SymbolKind::Native(_) => false,
                            SymbolKind::Let(_) | SymbolKind::Parameter(_, _) => true,
                        },
                        Some(param_types) => match &symbol.kind {
                            SymbolKind::Let(_) | SymbolKind::Parameter(_, _) => false,
                            SymbolKind::LetFn(_, ref fn_param_type, _) => {
                                param_types == fn_param_type.as_slice()
                            }
                            SymbolKind::Native(native) => {
                                param_types == native.parameters().as_slice()
                            }
                        },
                    }
                })
                .copied()
        })
    }
}

#[derive(Debug)]
pub struct Symbol {
    id: SymbolId,
    kind: SymbolKind,
    ty: Type,
}

impl Symbol {
    pub fn kind(&self) -> &SymbolKind {
        &self.kind
    }

    pub fn ty(&self) -> Type {
        self.ty
    }
}

#[derive(Debug)]
pub enum SymbolKind {
    Let(StmtId),
    LetFn(StmtId, Vec<Type>, Type),
    Parameter(StmtId, usize),
    Native(Native),
}

// todo think about it being Copy
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum Type {
    Boolean,
    // fixme this is not enough
    Function,
    Number,

    /// This value is used when the statement/expression does not have any value. This is the
    /// case for `let` and `let fn`.
    Void,

    /// This value is used when the statement/expression does not return any value. This is the
    /// case for `ret`.
    None,
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function => write!(f, "function"),
            Type::Number => write!(f, "number"),
            Type::Void => write!(f, "void"),
            Type::None => write!(f, "no type"),
        }
    }
}

impl TryFrom<&str> for Type {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "boolean" => Ok(Type::Boolean),
            "function" => Ok(Type::Function),
            "number" => Ok(Type::Number),
            "void" => Ok(Type::Void),
            &_ => Err(format!("'{}' is not a known type", value)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::desugar::ImplicitRet;
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
        let ast = Parser::new(Lexer::new("let x(n: number): number = { n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_ref_to_let() {
        let ast = Parser::new(Lexer::new("let x(): number = { let n = 0; n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let ast = Parser::new(Lexer::new("let x() = { } x();"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new())
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
        .convert_implicit_ret(ImplicitRet::new())
        .resolve(Resolver::new(), Natives::default())
        .unwrap();

        assert_snapshot!(XmlWriter::new(&ast).serialize());
    }

    #[test]
    fn resolve_missing_def() {
        let actual_diagnostics = Parser::new(Lexer::new("let x() = { n; }"))
            .parse()
            .unwrap()
            .convert_implicit_ret(ImplicitRet::new())
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
            .convert_implicit_ret(ImplicitRet::new())
            .resolve(Resolver::new(), Natives::default())
            .unwrap();

        assert_snapshot!("rebinding-xml", XmlWriter::new(&ast).serialize());
        assert_snapshot!("rebinding-dot", Dot::new(&ast).serialize());
    }

    macro_rules! test_type_error {
        ($name:ident, $src:expr, $error:expr, $span:expr) => {
            #[test]
            fn $name() {
                let actual_diagnostics = Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRet::new())
                    .resolve(Resolver::new(), Natives::default())
                    .unwrap_err();
                //
                // let actual_diagnostics = Resolver::new(ast, Natives::default())
                //     .resolve()
                //     .expect_err("err expected");

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
                Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRet::new())
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
    // fixme un-comment the following test
    // test_type_ok!(
    //     assign_from_native,
    //     "let n = add;"
    // );
}
