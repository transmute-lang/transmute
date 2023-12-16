use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId};
use crate::ast::literal::LiteralKind;
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::{Parameter, StatementKind};
use crate::ast::Ast;
use crate::error::Diagnostics;
use crate::exit_points::ExitPoints;
use crate::lexer::Span;
use crate::natives::{Native, Natives};
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{Display, Formatter};
use std::rc::Rc;

pub struct Resolver {
    ast: Ast,
    symbols: Rc<RefCell<Vec<Symbol>>>,
    expression_types: Vec<Option<Result<Type, ()>>>,
    diagnostics: Diagnostics,
    scope_stack: Vec<Scope>,
}

impl Resolver {
    pub fn new(ast: Ast, natives: Natives) -> Self {
        let ast = ast.merge(Into::<Ast>::into(&natives));
        let expression_count = ast.expressions_count();
        let symbols = Rc::new(RefCell::new(Vec::<Symbol>::new()));
        let mut me = Self {
            ast,
            symbols: symbols.clone(),
            expression_types: vec![None; expression_count],
            diagnostics: Default::default(),
            scope_stack: vec![Scope::new(symbols)],
        };

        for native in natives.into_iter() {
            let ident = me.ast.identifier_id(native.name());
            let ret_type = native.return_type();
            me.insert_symbol(ident, SymbolKind::Native(native), ret_type);
        }

        me
    }

    pub fn resolve(mut self) -> Result<(Ast, Vec<Symbol>), Diagnostics> {
        let stmts = self.ast.statements().to_vec();

        self.insert_functions(&stmts);

        let _ = self.resolve_statements(&stmts);

        if self.diagnostics.is_empty() {
            Ok((self.ast, self.symbols.replace(vec![])))
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
                let parameter_types = params
                    .iter()
                    .filter_map(|p| match Type::try_from(self.ast.identifier(p.ty().id())) {
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
                    .map(|t| match Type::try_from(self.ast.identifier(t.id())) {
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
                            ident.id(),
                            SymbolKind::LetFn(*stmt, parameter_types, ret_type),
                            Type::Function,
                        );
                    }
                }
            }
        }
    }

    fn insert_symbol(&mut self, ident: IdentId, kind: SymbolKind, ty: Type) {
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

    fn resolve_expression(&mut self, expr: ExprId) -> Result<Type, ()> {
        let expr_id = expr.id();
        if let Some(ty) = self.expression_types[expr_id] {
            return ty;
        }

        let expr = self.ast.expression(expr);
        let ty = match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                self.resolve_assignment(*ident_ref, *expr)
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.resolve_if(*cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(literal) => self.resolve_literal(literal.kind().clone()),
            ExpressionKind::Binary(left, op, right) => {
                self.resolve_binary(expr.id(), expr.span().clone(), *left, op.clone(), *right)
            }
            ExpressionKind::Unary(op, operand) => {
                self.resolve_unary(expr.id(), expr.span().clone(), op.clone(), *operand)
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.resolve_function_call(*ident_ref, params.to_vec().as_slice())
            }
            ExpressionKind::While(cond, expr) => self.resolve_while(*cond, *expr),
            ExpressionKind::Block(stmts) => self.resolve_block(&stmts.to_vec()),
            ExpressionKind::Dummy => {
                panic!()
            }
        };

        self.expression_types[expr_id] = Some(ty);
        ty
    }

    fn resolve_assignment(&mut self, ident_ref: IdentRefId, expr: ExprId) -> Result<Type, ()> {
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
        //  - assign to a parameter

        let expr_type = self.resolve_expression(expr)?;

        let expected_type = self
            // todo: to search for method, we need to extract the parameter types from the
            //  expr_type, it it corresponds to a function type. We don't have this
            //  information yet and this we cannot assign to a variable holding a function
            //  (yet).
            .resolve_ident_ref(ident_ref, None)
            .map(|s| self.symbols.borrow()[s.id()].ty)
            .ok_or(())?;

        if expr_type != expected_type {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", expected_type, expr_type),
                self.ast.expression(expr).span().clone(),
                (file!(), line!()),
            );
            return Err(());
        }

        Ok(expr_type)
    }

    fn resolve_if(
        &mut self,
        cond: ExprId,
        true_branch: ExprId,
        false_branch: Option<ExprId>,
    ) -> Result<Type, ()> {
        let cond_type = self.resolve_expression(cond)?;

        if cond_type != Type::Boolean {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", Type::Boolean, cond_type),
                self.ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        let true_branch_type = self.resolve_expression(true_branch)?;
        let false_branch_type = false_branch
            .map(|e| self.resolve_expression(e))
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
                let false_branch = self
                    .ast
                    .expression(false_branch.expect("false branch exists"));
                self.diagnostics.report_err(
                    format!("Expected type {tt}, got {ft}"),
                    false_branch.span().clone(),
                    (file!(), line!()),
                );
                Err(())
            }
        }
    }

    fn resolve_literal(&mut self, literal: LiteralKind) -> Result<Type, ()> {
        match literal {
            LiteralKind::Boolean(_) => Ok(Type::Boolean),
            LiteralKind::Number(_) => Ok(Type::Number),
            LiteralKind::Identifier(ident_ref) => {
                // todo things to check:
                //  - behaviour when target is let fn
                //  - behaviour when target is a native
                // todo resolve function ref, see comment in resolve_assignment
                self.resolve_ident_ref(ident_ref, None)
                    .map(|s| self.symbols.borrow()[s.id()].ty)
                    .ok_or(())
            }
        }
    }

    fn resolve_binary(
        &mut self,
        expr: ExprId,
        expr_span: Span,
        left: ExprId,
        op: BinaryOperator,
        right: ExprId,
    ) -> Result<Type, ()> {
        let left_type = self.resolve_expression(left)?;
        let right_type = self.resolve_expression(right)?;

        let ident_id = self.ast.identifier_id(op.kind().function_name());
        let symbol = self
            .resolve_ident(ident_id, Some(&[left_type, right_type]), op.span())
            .ok_or(())?;

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

    fn resolve_unary(
        &mut self,
        expr: ExprId,
        expr_span: Span,
        op: UnaryOperator,
        operand: ExprId,
    ) -> Result<Type, ()> {
        let operand_type = self.resolve_expression(operand)?;

        let ident_id = self.ast.identifier_id(op.kind().function_name());
        let symbol = self
            .resolve_ident(ident_id, Some(&[operand_type]), op.span())
            .ok_or(())?;

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

    fn resolve_function_call(
        &mut self,
        ident_ref: IdentRefId,
        params: &[ExprId],
    ) -> Result<Type, ()> {
        let param_types = params
            .iter()
            .filter_map(|e| self.resolve_expression(*e).ok())
            .collect::<Vec<Type>>();

        if param_types.len() != params.len() {
            return Err(());
        }

        self.resolve_ident_ref(ident_ref, Some(&param_types))
            .map(|s| match &self.symbols.borrow()[s.id()].kind {
                SymbolKind::LetFn(_, _, ret_type) => Ok(*ret_type),
                SymbolKind::Native(native) => Ok(native.return_type()),
                SymbolKind::Let(_) | SymbolKind::Parameter(_, _) => {
                    panic!("the resolved symbol was not a function")
                }
            })
            .ok_or(())?
    }

    fn resolve_while(&mut self, cond: ExprId, expr: ExprId) -> Result<Type, ()> {
        let cond_type = self.resolve_expression(cond)?;

        if cond_type != Type::Boolean {
            self.diagnostics.report_err(
                format!("Expected type {}, got {}", Type::Boolean, cond_type),
                self.ast.expression(cond).span().clone(),
                (file!(), line!()),
            );
        }

        self.resolve_expression(expr)
    }

    fn resolve_block(&mut self, stmts: &[StmtId]) -> Result<Type, ()> {
        self.push_scope();

        self.insert_functions(stmts);
        let ret_type = self.resolve_statements(stmts);

        self.pop_scope();

        ret_type
    }

    fn resolve_statements(&mut self, stmts: &[StmtId]) -> Result<Type, ()> {
        let mut ret_type = Ok(Type::Void);

        for stmt in stmts.iter() {
            let stmt_type = match self.ast.statement(*stmt).kind() {
                StatementKind::Expression(expr) => self.resolve_expression(*expr),
                StatementKind::Let(ident, expr) => {
                    self.resolve_let(*stmt, ident.id(), *expr);
                    Ok(Type::Void)
                }
                StatementKind::Ret(expr) => {
                    let _ = self.resolve_expression(*expr);
                    Ok(Type::None)
                }
                StatementKind::LetFn(_ident, params, ret_type, expr) => {
                    self.resolve_function(
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

    fn resolve_let(&mut self, stmt: StmtId, ident: IdentId, expr: ExprId) {
        match self.resolve_expression(expr) {
            Ok(Type::None) => {
                let expr = self.ast.expression(expr);
                self.diagnostics.report_err(
                    format!("Expected some type, got {}", Type::None),
                    expr.span().clone(),
                    (file!(), line!()),
                );
            }
            Ok(t) => {
                self.insert_symbol(ident, SymbolKind::Let(stmt), t);
            }
            Err(_) => {}
        }
    }

    fn resolve_function(
        &mut self,
        stmt: StmtId,
        params: &[Parameter],
        ret_type: Option<&Identifier>,
        expr: ExprId,
    ) {
        self.push_scope();

        let ret_type = ret_type
            .map(|t| match Type::try_from(self.ast.identifier(t.id())) {
                Ok(t) => t,
                Err(_) => {
                    // no need to report error here, it was already reported in insert_functions
                    Type::Void
                }
            })
            .unwrap_or(Type::Void);

        for (index, parameter) in params.iter().enumerate() {
            let ty = match Type::try_from(self.ast.identifier(parameter.ty().id())) {
                Ok(ty) => ty,
                Err(_) => {
                    // no need to report error here, it was already reported in insert_functions
                    Type::Void
                }
            };

            self.insert_symbol(
                parameter.identifier().id(),
                SymbolKind::Parameter(stmt, index),
                ty,
            )
        }

        let _ = self.resolve_expression(expr);

        let exit_points = ExitPoints::new(&self.ast).exit_points(expr);
        if exit_points.is_empty() {
            if ret_type != Type::Void {
                let stmt = self.ast.statement(stmt);
                self.diagnostics.report_err(
                    format!("Expected type {ret_type}, got void"),
                    stmt.span().clone(),
                    (file!(), line!()),
                );
            }
        } else {
            for expr in exit_points {
                match self.resolve_expression(expr) {
                    Ok(Type::None) => panic!("functions must not return {}", Type::None),
                    Ok(ty) => {
                        if ty != ret_type {
                            let expr = self.ast.expression(expr);
                            self.diagnostics.report_err(
                                format!("Expected type {ret_type}, got {ty}"),
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
        ident_ref: IdentRefId,
        param_types: Option<&[Type]>,
    ) -> Option<SymbolId> {
        let ident_ref = self.ast.identifier_ref(ident_ref);

        if let Some(symbol) = ident_ref.symbol_id() {
            return Some(symbol);
        }

        let ident = ident_ref.ident().id();
        match self
            .scope_stack
            .iter()
            .rev()
            .find_map(|scope| scope.find(&ident, param_types))
        {
            Some(s) => {
                let mut ident_ref = ident_ref.clone();
                ident_ref.set_symbol_id(s);
                self.ast.replace_identifier_ref(ident_ref);
                Some(s)
            }
            None => {
                // todo nice to have: propose known alternatives
                if let Some(param_types) = param_types {
                    self.diagnostics.report_err(
                        format!(
                            "No function '{}' found for parameters of types ({})",
                            self.ast.identifier(ident),
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
                        format!("No variable '{}' found", self.ast.identifier(ident)),
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
                            self.ast.identifier(ident),
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
                        format!("No variable '{}' found", self.ast.identifier(ident)),
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
        self.symbols
            .get(ident)
            .and_then(|symbols| {
                let filtered_symbols = symbols
                    .iter()
                    .filter(|s| {
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
                    .collect::<Vec<&SymbolId>>();

                if filtered_symbols.len() > 1 {
                    return None;
                }

                filtered_symbols.first().copied()
            })
            .copied()
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
    Void,
    // fixme once expressions/statements are merged, update the doc
    /// This value is used when the statement/expression does not return any value. This is the
    /// case of `ret` for instance.
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

        let (ast, symbols) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("no error expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols).serialize());
    }

    #[test]
    fn resolve_ref_to_let() {
        let (ast, diagnostics) =
            Parser::new(Lexer::new("let x(): number = { let n = 0; n; }")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols).serialize());
    }

    #[test]
    fn resolve_ref_to_let_fn() {
        let (ast, diagnostics) = Parser::new(Lexer::new("let x() = { } x();")).parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols).serialize());
    }

    #[test]
    fn resolve_ref_to_parameter_nested() {
        let (ast, diagnostics) = Parser::new(Lexer::new(
            "let x(n: number): number = { while true { ret n; } }",
        ))
        .parse();
        assert!(diagnostics.is_empty(), "{:?}", diagnostics);

        let (ast, symbols) = Resolver::new(ast, Natives::default())
            .resolve()
            .expect("ok expected");

        assert_snapshot!(XmlWriter::new(&ast, &symbols).serialize());
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
                // let natives = Natives::default();

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
