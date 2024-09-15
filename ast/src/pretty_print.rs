use crate::expression::{Expression, ExpressionKind, Target};
use crate::literal::{Literal, LiteralKind};
use crate::operators::{BinaryOperatorKind, UnaryOperatorKind};
use crate::statement::{RetMode, Statement, StatementKind};
use crate::Ast;
use std::fmt::{Result, Write};
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId};

pub trait PrettyPrint {
    fn pretty_print<W>(
        &self,
        ctx: &mut PrettyPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> Result
    where
        W: Write;
}

#[derive(Default)]
pub struct Options {
    pub display_implicit_ret: bool,
}

impl PrettyPrint for Literal {
    fn pretty_print<W>(
        &self,
        ctx: &mut PrettyPrintContext<'_>,
        _opts: &Options,
        f: &mut W,
    ) -> Result
    where
        W: Write,
    {
        match &self.kind {
            LiteralKind::Boolean(b) => {
                write!(f, "{b}")
            }
            LiteralKind::Identifier(ident) => {
                write!(f, "{ident}", ident = ctx.identifier_ref(*ident))
            }
            LiteralKind::Number(n) => {
                write!(f, "{n}")
            }
        }
    }
}

impl PrettyPrint for Expression {
    fn pretty_print<W>(&self, ctx: &mut PrettyPrintContext<'_>, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        match &self.kind {
            ExpressionKind::Assignment(Target::Direct(target), expr_id) => {
                write!(f, "{ident} = ", ident = ctx.identifier_ref(*target))?;
                ctx.pretty_print_expression(*expr_id, opts, f)
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                ctx.pretty_print_expression(*lhs_expr_id, opts, f)?;
                write!(f, " = ")?;
                ctx.pretty_print_expression(*rhs_expr_id, opts, f)
            }
            ExpressionKind::If(cond_id, true_id, false_id) => {
                let indent = ctx.indent();
                // todo improve else/if chains
                write!(f, "if ")?;
                ctx.pretty_print_expression(*cond_id, opts, f)?;
                writeln!(f, " {{")?;
                ctx.level += 1;
                ctx.pretty_print_expression(*true_id, opts, f)?;
                ctx.level -= 1;
                write!(f, "{indent}}}")?;

                if let Some(false_id) = false_id {
                    writeln!(f, "\n{indent}else {{")?;
                    ctx.level += 1;
                    ctx.pretty_print_expression(*false_id, opts, f)?;
                    ctx.level -= 1;
                    write!(f, "{indent}}}")?;
                }

                ctx.require_semicolon = false;

                Ok(())
            }
            ExpressionKind::Literal(lit) => lit.pretty_print(ctx, opts, f),
            ExpressionKind::Binary(left_id, op, right_id) => {
                ctx.pretty_print_expression(*left_id, opts, f)?;

                match &op.kind {
                    BinaryOperatorKind::Addition => write!(f, " + "),
                    BinaryOperatorKind::Division => write!(f, " / "),
                    BinaryOperatorKind::Equality => write!(f, " == "),
                    BinaryOperatorKind::GreaterThan => write!(f, " > "),
                    BinaryOperatorKind::GreaterThanOrEqualTo => write!(f, " >= "),
                    BinaryOperatorKind::Multiplication => write!(f, " * "),
                    BinaryOperatorKind::NonEquality => write!(f, " != "),
                    BinaryOperatorKind::SmallerThan => write!(f, " < "),
                    BinaryOperatorKind::SmallerThanOrEqualTo => write!(f, " <= "),
                    BinaryOperatorKind::Subtraction => write!(f, " - "),
                }?;

                ctx.pretty_print_expression(*right_id, opts, f)
            }
            ExpressionKind::Unary(op, expr_id) => {
                match &op.kind {
                    UnaryOperatorKind::Minus => {
                        write!(f, "-")?;
                    }
                }
                ctx.pretty_print_expression(*expr_id, opts, f)
            }
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                write!(f, ".")?;
                write!(f, "{ident}", ident = ctx.identifier_ref(*ident_ref_id))
            }
            ExpressionKind::FunctionCall(ident_ref_id, param_ids) => {
                write!(f, "{ident}(", ident = ctx.identifier_ref(*ident_ref_id))?;
                for (i, param) in param_ids.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    ctx.pretty_print_expression(*param, opts, f)?;
                }
                write!(f, ")")
            }
            ExpressionKind::While(cond_id, expr_id) => {
                write!(f, "while ")?;
                ctx.pretty_print_expression(*cond_id, opts, f)?;
                writeln!(f, " {{")?;
                ctx.level += 1;
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                ctx.level -= 1;
                write!(f, "{indent}}}", indent = ctx.indent())?;

                ctx.require_semicolon = false;

                Ok(())
            }
            ExpressionKind::Block(stmt_ids) => {
                for stmt_id in stmt_ids {
                    ctx.pretty_print_statement(*stmt_id, opts, f)?;
                }
                Ok(())
            }
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                write!(f, "{} {{", ctx.identifier_ref(*ident_ref_id))?;
                for (i, (ident_ref_id, expr_id)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}: ", ctx.identifier_ref(*ident_ref_id))?;
                    ctx.pretty_print_expression(*expr_id, opts, f)?;
                    write!(f, ",")?;
                }
                write!(f, "}}")
            }
            ExpressionKind::Dummy => unreachable!(),
        }
    }
}

impl PrettyPrint for Statement {
    fn pretty_print<W>(&self, ctx: &mut PrettyPrintContext<'_>, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        match &self.kind {
            StatementKind::Expression(expr_id) => {
                write!(f, "{indent}", indent = ctx.indent())?;
                ctx.require_semicolon = true;
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                if ctx.require_semicolon {
                    writeln!(f, ";")
                } else {
                    writeln!(f)
                }
            }
            StatementKind::Let(ident, expr_id) => {
                write!(
                    f,
                    "{indent}let {ident} = ",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                writeln!(f, ";")
            }
            StatementKind::Ret(Some(expr_id), mode) => {
                match mode {
                    RetMode::Implicit if !opts.display_implicit_ret => {
                        write!(f, "{indent}", indent = ctx.indent())?;
                        ctx.pretty_print_expression(*expr_id, opts, f)?;
                    }
                    _ => {
                        write!(f, "{indent}ret ", indent = ctx.indent())?;
                        ctx.pretty_print_expression(*expr_id, opts, f)?;
                    }
                }
                writeln!(f, ";")
            }
            StatementKind::Ret(None, mode) => {
                match mode {
                    RetMode::Implicit if !opts.display_implicit_ret => {
                        write!(f, "{indent}", indent = ctx.indent())?;
                    }
                    _ => {
                        write!(f, "{indent}ret ", indent = ctx.indent())?;
                    }
                }
                writeln!(f, ";")
            }
            StatementKind::LetFn(ident, parameters, ret_type, expr_id) => {
                let indent = ctx.indent();
                write!(f, "{indent}let {ident}(", ident = ctx.identifier(ident.id))?;

                for (i, parameter) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(
                        f,
                        "{ident}: {ty}",
                        ident = ctx.identifier(parameter.identifier.id),
                        ty = ctx.identifier_ref(parameter.ty)
                    )?;
                }

                write!(f, ")")?;
                if let Some(ret_type) = ret_type.ret {
                    write!(f, ": {ret_type}", ret_type = ctx.identifier_ref(ret_type))?;
                }
                writeln!(f, " = {{")?;
                ctx.level += 1;
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                ctx.level -= 1;
                writeln!(f, "{indent}}}")
            }
            StatementKind::Struct(ident, fields) => {
                let indent = ctx.indent();
                writeln!(
                    f,
                    "{indent}struct {ident} {{",
                    ident = ctx.identifier(ident.id)
                )?;

                for field in fields.iter() {
                    writeln!(
                        f,
                        "{indent}  {ident}: {ty},",
                        ident = ctx.identifier(field.identifier.id),
                        ty = ctx.identifier_ref(field.ty())
                    )?;
                }
                writeln!(f, "{indent}}}")
            }
        }
    }
}

impl Ast {
    pub fn pretty_print<W>(&self, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        let mut ctx = PrettyPrintContext {
            ast: self,
            level: 0,
            require_semicolon: false,
        };
        for stmt_id in self.roots.iter() {
            ctx.pretty_print_statement(*stmt_id, opts, f)?;
        }
        Ok(())
    }
}

pub struct PrettyPrintContext<'a> {
    ast: &'a Ast,
    level: usize,
    require_semicolon: bool,
}

impl PrettyPrintContext<'_> {
    fn indent(&self) -> String {
        "  ".repeat(self.level)
    }

    fn identifier(&self, ident_id: IdentId) -> &str {
        &self.ast.identifiers[ident_id]
    }

    fn identifier_ref(&self, ident_ref_id: IdentRefId) -> &str {
        self.identifier(self.ast.identifier_refs[ident_ref_id].ident.id)
    }

    fn pretty_print_expression<W>(&mut self, expr_id: ExprId, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        self.ast.expressions[expr_id].pretty_print(self, opts, f)
    }

    fn pretty_print_statement<W>(&mut self, stmt_id: StmtId, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        self.ast.statements[stmt_id].pretty_print(self, opts, f)
    }
}

#[cfg(test)]
mod tests {
    use crate::identifier::Identifier;
    use crate::identifier_ref::IdentifierRef;
    use crate::lexer::Lexer;
    use crate::literal::{Literal, LiteralKind};
    use crate::parser::Parser;
    use crate::pretty_print::{Options, PrettyPrint, PrettyPrintContext};
    use crate::Ast;
    use insta::assert_snapshot;
    use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId};
    use transmute_core::span::Span;

    macro_rules! identifiers {
    ($expr:expr) => {vec![$expr.to_string()]};
    ($expr:expr, $($tail:tt)*) => {{
        let mut v = identifiers!($expr);
        v.append(&mut identifiers!($($tail)*));
        v
    }};
}

    macro_rules! identifier_refs {
    ($ident:expr) => {
        identifier_refs!(0 => $ident)
    };
    ($ident:expr, $($tail:tt)*) => {
        identifier_refs!(0 => $ident, $($tail)*)
    };
    ($ident_ref:expr => $ident:expr) => {
        vec![IdentifierRef::new(
            IdentRefId::from($ident_ref),
            Identifier::new(IdentId::from($ident), Span::default())
        )]
    };
    ($ident_ref:expr => $ident:expr, $($tail:tt)*) => {{
        let mut v = identifier_refs!($ident_ref, $ident);
        v.append(&mut identifier_refs!($ident_ref + 1 => $($tail)*));
        v
    }};
}

    #[test]
    fn literal_boolean() {
        let ast = Ast::new(vec![], vec![], vec![], vec![], vec![]);

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let lit = Literal::new(LiteralKind::Boolean(false), Span::default());
        let mut w = String::new();
        lit.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "false");
    }

    #[test]
    fn literal_number() {
        let ast = Ast::new(vec![], vec![], vec![], vec![], vec![]);

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let lit = Literal::new(LiteralKind::Number(1), Span::default());
        let mut w = String::new();
        lit.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "1");
    }

    #[test]
    fn literal_ident() {
        let ast = Ast::new(
            identifiers!["ident"],
            identifier_refs!(0),
            vec![],
            vec![],
            vec![],
        );

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };

        let lit = Literal::new(
            LiteralKind::Identifier(IdentRefId::from(0)),
            Span::default(),
        );
        let mut w = String::new();
        lit.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "ident");
    }

    #[test]
    fn expression_assignment() {
        let ast = Parser::new(Lexer::new("a = true;")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "a = true");
    }

    #[test]
    fn expression_assignment_indirect() {
        let ast = Parser::new(Lexer::new("a.b.c = true;")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(ast.expressions.len() - 1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "a.b.c = true");
    }

    #[test]
    fn expression_unary() {
        let ast = Parser::new(Lexer::new("-a;")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "-a");
    }

    #[test]
    fn expression_binary() {
        let ast = Parser::new(Lexer::new("a+b;")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(2)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "a + b");
    }

    #[test]
    fn expression_function_call_0() {
        let ast = Parser::new(Lexer::new("f();")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(0)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "f()");
    }

    #[test]
    fn expression_function_call_1() {
        let ast = Parser::new(Lexer::new("f(1);")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "f(1)");
    }

    #[test]
    fn expression_function_call_2() {
        let ast = Parser::new(Lexer::new("f(1,2);")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(2)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "f(1, 2)");
    }

    #[test]
    fn expression_while() {
        let ast = Parser::new(Lexer::new("while true { 1; }"))
            .parse()
            .unwrap();
        let expr = &ast.expressions[ExprId::from(3)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"while true {
    1;
  }"#
        );
    }

    #[test]
    fn expression_if() {
        let ast = Parser::new(Lexer::new("if true { 1; }")).parse().unwrap();
        let expr = &ast.expressions[ExprId::from(3)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"if true {
    1;
  }"#
        );
    }

    #[test]
    fn expression_if_else() {
        let ast = Parser::new(Lexer::new("if true { 1; } else { 2; }"))
            .parse()
            .unwrap();
        let expr = &ast.expressions[ExprId::from(5)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"if true {
    1;
  }
  else {
    2;
  }"#
        );
    }

    #[test]
    fn expression_if_else_if() {
        let ast = Parser::new(Lexer::new("if true { 1; } else if b { 2; }"))
            .parse()
            .unwrap();
        let expr = &ast.expressions[ExprId::from(8)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"if true {
    1;
  }
  else {
    if b {
      2;
    }
  }"#
        );
    }

    #[test]
    fn expression_if_else_if_else() {
        let ast = Parser::new(Lexer::new("if true { 1; } else if b { 2; } else { 3; }"))
            .parse()
            .unwrap();
        let expr = &ast.expressions[ExprId::from(10)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"if true {
    1;
  }
  else {
    if b {
      2;
    }
    else {
      3;
    }
  }"#
        );
    }

    #[test]
    fn statement_expression() {
        let ast = Parser::new(Lexer::new("1;")).parse().unwrap();
        let stmt = &ast.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "  1;\n");
    }

    #[test]
    fn statement_let() {
        let ast = Parser::new(Lexer::new("let a = 1;")).parse().unwrap();
        let stmt = &ast.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "  let a = 1;\n");
    }

    #[test]
    fn statement_ret_explicit() {
        let ast = Parser::new(Lexer::new("ret a;")).parse().unwrap();
        let stmt = &ast.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "  ret a;\n");
    }

    #[test]
    fn statement_ret_implicit() {
        let ast = Parser::new(Lexer::new("let f() = { a; }")).parse().unwrap();
        let stmt = &ast.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "  a;\n");
    }

    #[test]
    fn statement_let_fn() {
        let ast = Parser::new(Lexer::new("let f() = { a; }")).parse().unwrap();
        let stmt = &ast.statements[StmtId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"  let f() = {
    a;
  }
"#
        );
    }

    #[test]
    fn statement_let_fn_ret_type() {
        let ast = Parser::new(Lexer::new("let f(): number = { a; }"))
            .parse()
            .unwrap();
        let stmt = &ast.statements[StmtId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"  let f(): number = {
    a;
  }
"#
        );
    }

    #[test]
    fn statement_let_fn_param_1() {
        let ast = Parser::new(Lexer::new("let f(x: number) = { a; }"))
            .parse()
            .unwrap();
        let stmt = &ast.statements[StmtId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"  let f(x: number) = {
    a;
  }
"#
        );
    }

    #[test]
    fn statement_let_fn_param_2() {
        let ast = Parser::new(Lexer::new("let f(x: number, y: number) = { a; }"))
            .parse()
            .unwrap();
        let stmt = &ast.statements[StmtId::from(1)];

        let mut ctx = PrettyPrintContext {
            ast: &ast,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        stmt.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(
            w,
            r#"  let f(x: number, y: number) = {
    a;
  }
"#
        );
    }

    #[test]
    fn fibonacci_rec() {
        let ast = Parser::new(Lexer::new(
            "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;",
        ))
        .parse()
        .unwrap();

        let mut w = String::new();

        ast.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn fibonacci_iter() {
        let ast = Parser::new(Lexer::new("let f(n: number): number = {if n == 0 { ret 0; }if n == 1 { ret 1; }let prev_prev = 0;let prev = 1;let current = 0;while n > 1 {current = prev_prev + prev;prev_prev = prev;prev = current;n = n - 1;}current;}f(9) + 8;"))
            .parse()
            .unwrap();

        let mut w = String::new();

        ast.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_declaration() {
        let ast = Parser::new(Lexer::new("struct Point { x: number, y: number }"))
            .parse()
            .unwrap();

        let mut w = String::new();

        ast.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_instantiation() {
        let ast = Parser::new(Lexer::new("Point { x: 1, y: 2 };"))
            .parse()
            .unwrap();

        let mut w = String::new();

        ast.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_nested_access() {
        let ast = Parser::new(Lexer::new("s.f.g;")).parse().unwrap();

        let mut w = String::new();

        ast.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }
}
