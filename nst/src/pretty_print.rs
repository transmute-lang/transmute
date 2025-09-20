use crate::nodes::{Expression, ExpressionKind, Nst, Target};
use crate::nodes::{Literal, LiteralKind};
use crate::nodes::{RetMode, Statement, StatementKind, TypeDefKind};
use std::fmt::{Result, Write};
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, TypeDefId};

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
            LiteralKind::String(n) => {
                // todo:feature handle escapes
                write!(f, "\"{n}\"")
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
                // todo:ux improve else/if chains
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
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                write!(f, ".")?;
                write!(f, "{ident}", ident = ctx.identifier_ref(*ident_ref_id))
            }
            ExpressionKind::FunctionCall(expr_id, param_ids) => {
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                write!(f, "(")?;
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
            ExpressionKind::ArrayInstantiation(values) => {
                write!(f, "[")?;
                for (i, expr_id) in values.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    ctx.pretty_print_expression(*expr_id, opts, f)?;
                    write!(f, ",")?;
                }
                write!(f, "]")
            }
            ExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => {
                ctx.pretty_print_expression(*base_expr_id, opts, f).unwrap();
                write!(f, "[")?;
                ctx.pretty_print_expression(*index_expr_id, opts, f)
                    .unwrap();
                write!(f, "]")
            }
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
            StatementKind::Namespace(ident, _, stmts) => {
                if ctx.identifier(ident.id) != "<root>" {
                    writeln!(
                        f,
                        "{indent}namespace {ident} {{",
                        indent = ctx.indent(),
                        ident = ctx.identifier(ident.id)
                    )?;
                    ctx.level += 1;
                }

                for stmt in stmts {
                    ctx.pretty_print_statement(*stmt, opts, f)?;
                }

                if ctx.identifier(ident.id) != "<root>" {
                    ctx.level -= 1;
                    writeln!(f, "{indent}}}", indent = ctx.indent(),)?;
                }

                Ok(())
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
            StatementKind::LetFn(ident, annotations, parameters, ret_type, expr_id) => {
                let indent = ctx.indent();
                for annotation in annotations {
                    writeln!(
                        f,
                        "{indent}@{ident}",
                        ident = annotation
                            .ident_ref_ids
                            .iter()
                            .map(|ident_ref_id| ctx.identifier_ref(*ident_ref_id))
                            .collect::<Vec<_>>()
                            .join("."),
                    )?;
                }
                write!(f, "{indent}let {ident}(", ident = ctx.identifier(ident.id))?;

                for (i, parameter) in parameters.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(
                        f,
                        "{ident}: ",
                        ident = ctx.identifier(parameter.identifier.id),
                    )?;
                    parameter.type_def_id.pretty_print(ctx, opts, f)?;
                }

                write!(f, ")")?;
                if let Some(ret_type) = &ret_type.type_def_id {
                    write!(f, ": ",)?;
                    ret_type.pretty_print(ctx, opts, f)?;
                }
                writeln!(f, " = {{")?;
                ctx.level += 1;
                ctx.pretty_print_expression(*expr_id, opts, f)?;
                ctx.level -= 1;
                writeln!(f, "{indent}}}")
            }
            StatementKind::Struct(ident, annotations, fields) => {
                let indent = ctx.indent();
                for annotation in annotations {
                    writeln!(
                        f,
                        "{indent}@{ident}",
                        ident = annotation
                            .ident_ref_ids
                            .iter()
                            .map(|ident_ref| ctx.identifier_ref(*ident_ref))
                            .collect::<Vec<_>>()
                            .join(".")
                    )?;
                }
                writeln!(
                    f,
                    "{indent}struct {ident} {{",
                    ident = ctx.identifier(ident.id)
                )?;

                for field in fields.iter() {
                    write!(
                        f,
                        "{indent}  {ident}: ",
                        ident = ctx.identifier(field.identifier.id),
                    )?;
                    field.type_def_id.pretty_print(ctx, opts, f)?;
                    writeln!(f, ",")?;
                }
                writeln!(f, "{indent}}}")
            }
            StatementKind::Use(ident) => {
                let indent = ctx.indent();
                writeln!(
                    f,
                    "{indent}use {ident};",
                    ident = ident
                        .iter()
                        .map(|ident_ref_id| ctx.identifier_ref(*ident_ref_id))
                        .collect::<Vec<_>>()
                        .join(".")
                )
            }
            StatementKind::Annotation(ident) => {
                let indent = ctx.indent();
                writeln!(
                    f,
                    "{indent}annotation {ident};",
                    ident = ctx.identifier(ident.id)
                )
            }
        }
    }
}

impl PrettyPrint for TypeDefId {
    fn pretty_print<W>(&self, ctx: &mut PrettyPrintContext<'_>, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        match &ctx.nst.type_defs[*self].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                write!(
                    f,
                    "{}",
                    ident_ref_ids
                        .iter()
                        .map(|ident_ref| ctx.identifier_ref(*ident_ref))
                        .collect::<Vec<_>>()
                        .join(".")
                )
            }
            TypeDefKind::Array(base, len) => {
                write!(f, "[")?;
                base.pretty_print(ctx, opts, f)?;
                write!(f, "; {len}]")
            }
        }
    }
}

impl Nst {
    pub fn pretty_print<W>(&self, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        let mut ctx = PrettyPrintContext {
            nst: self,
            level: 0,
            require_semicolon: false,
        };
        ctx.pretty_print_statement(self.root, opts, f)?;
        Ok(())
    }
}

pub struct PrettyPrintContext<'a> {
    nst: &'a Nst,
    level: usize,
    require_semicolon: bool,
}

impl PrettyPrintContext<'_> {
    fn indent(&self) -> String {
        "  ".repeat(self.level)
    }

    fn identifier(&self, ident_id: IdentId) -> &str {
        &self.nst.identifiers[ident_id]
    }

    fn identifier_ref(&self, ident_ref_id: IdentRefId) -> &str {
        self.identifier(self.nst.identifier_refs[ident_ref_id].ident.id)
    }

    fn pretty_print_expression<W>(&mut self, expr_id: ExprId, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        self.nst.expressions[expr_id].pretty_print(self, opts, f)
    }

    fn pretty_print_statement<W>(&mut self, stmt_id: StmtId, opts: &Options, f: &mut W) -> Result
    where
        W: Write,
    {
        self.nst.statements[stmt_id].pretty_print(self, opts, f)
    }
}

#[cfg(test)]
mod tests {
    use crate::pretty_print::{Options, PrettyPrint, PrettyPrintContext};
    use crate::Nst;
    use insta::assert_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;
    use transmute_core::ids::{ExprId, StmtId};

    #[test]
    fn expression_assignment() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "a = true;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(1)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "a.b.c = true;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(nst.expressions.len() - 1)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
            level: 1,
            require_semicolon: false,
        };
        let mut w = String::new();
        expr.pretty_print(&mut ctx, &Options::default(), &mut w)
            .unwrap();
        assert_eq!(w, "a.b.c = true");
    }

    #[test]
    fn expression_function_call_0() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "f();"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(1)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "f(1);"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(2)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "f(1,2);"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(3)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "while true { 1; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(3)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "if true { 1; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(3)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "if true { 1; } else { 2; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(5)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "if true { 1; } else if b { 2; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(8)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(
                InputId::from(0),
                "if true { 1; } else if b { 2; } else { 3; }",
            ),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let expr = &nst.expressions[ExprId::from(10)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "1;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let a = 1;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "ret a;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(0)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f() = { a; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(1)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f() = { a; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(2)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(): number = { a; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(2)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(x: number) = { a; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(2)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(x: number, y: number) = { a; }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);
        let stmt = &nst.statements[StmtId::from(2)];

        let mut ctx = PrettyPrintContext {
            nst: &nst,
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
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(n: number): number = { if n <= 1 { ret n; } f(n - 1) + f(n - 2); } f(9) + 8;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn fibonacci_iter() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(n: number): number = {if n == 0 { ret 0; }if n == 1 { ret 1; }let prev_prev = 0;let prev = 1;let current = 0;while n > 1 {current = prev_prev + prev;prev_prev = prev;prev = current;n = n - 1;}current;}f(9) + 8;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_declaration() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "struct Point { x: number, y: number }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_instantiation() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "Point { x: 1, y: 2 };"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn struct_nested_access() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "s.f.g;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn array_instantiation() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "[1, 2, 3];"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn array_access() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "a[1];"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn array_access_dot_access() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "a[1].b;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn dot_access_array_access() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "a.b[1];"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn annotations() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "@a @b let f() {} @c @d.e.f struct S {}"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn nested_type() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "let f(p: a.b.c): ns1.ns2.type {}"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn use_simple() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "use a.b.c;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn namespace() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "namespace ns;"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }

    #[test]
    fn namespace_inline() {
        let mut compilation_unit = CompilationUnit::default();
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(InputId::from(0), "namespace ns { let f(): number { 1; } }"),
        )
        .parse();
        let ast = compilation_unit.into_ast().unwrap();
        let nst = Nst::from(ast);

        let mut w = String::new();

        nst.pretty_print(&Options::default(), &mut w).unwrap();

        assert_snapshot!(w);
    }
}
