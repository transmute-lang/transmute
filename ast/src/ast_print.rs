use crate::expression::{Expression, ExpressionKind, Target};
use crate::literal::{Literal, LiteralKind};
use crate::statement::{Statement, StatementKind, TypeDefKind};
use std::fmt::Write;
use transmute_core::id;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, TypeDefId};

pub trait AstPrint {
    fn ast_print<W>(
        &self,
        ctx: &mut AstPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write;
}

#[derive(Default)]
pub struct Options {}

impl AstPrint for Literal {
    fn ast_print<W>(
        &self,
        ctx: &mut AstPrintContext<'_>,
        _opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        match &self.kind {
            LiteralKind::Boolean(b) => {
                writeln!(f, "{indent}Bool: {b}", indent = ctx.indent())
            }
            LiteralKind::Identifier(ident) => {
                writeln!(
                    f,
                    "{indent}Ident: {ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier_ref(*ident)
                )
            }
            LiteralKind::Number(n) => {
                writeln!(f, "{indent}Number: {n}", indent = ctx.indent())
            }
            LiteralKind::String(n) => {
                writeln!(f, "{indent}String: {n}", indent = ctx.indent())
            }
        }
    }
}

impl AstPrint for Expression {
    fn ast_print<W>(
        &self,
        ctx: &mut AstPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        if let Some(tag) = ctx.tag.take() {
            writeln!(
                f,
                "{indent}{tag}:expr {id}",
                indent = ctx.indent(),
                id = id!(self.id)
            )?;
        } else {
            writeln!(
                f,
                "{indent}expr {id}",
                indent = ctx.indent(),
                id = id!(self.id)
            )?;
        }

        ctx.next_level();
        match &self.kind {
            ExpressionKind::Assignment(Target::Direct(target), expr_id) => {
                writeln!(
                    f,
                    "{indent}Assignment target={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier_ref(*target)
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                writeln!(f, "{indent}Assignment", indent = ctx.indent())?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("target");
                ctx.ast_print_expression(*lhs_expr_id, opts, f)?;
                ctx.tag = Some("value");
                ctx.last = true;
                ctx.ast_print_expression(*rhs_expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::If(cond_id, true_id, false_id) => {
                writeln!(f, "{indent}If", indent = ctx.indent())?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("cond");
                ctx.ast_print_expression(*cond_id, opts, f)?;

                ctx.tag = Some("true");
                ctx.last = !false_id.is_some();
                ctx.ast_print_expression(*true_id, opts, f)?;

                if let Some(false_id) = false_id {
                    ctx.tag = Some("false");
                    ctx.last = true;
                    ctx.ast_print_expression(*false_id, opts, f)?;
                }

                ctx.prev_level();
            }
            ExpressionKind::Literal(lit) => lit.ast_print(ctx, opts, f)?,
            ExpressionKind::Binary(left_id, op, right_id) => {
                writeln!(
                    f,
                    "{indent}Binary {op}",
                    indent = ctx.indent(),
                    op = op.kind.as_str()
                )?;

                ctx.last = true;
                ctx.next_level();
                ctx.tag = Some("lhs");
                ctx.ast_print_expression(*left_id, opts, f)?;
                ctx.tag = Some("rhs");
                ctx.last = true;
                ctx.ast_print_expression(*right_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::Unary(op, expr_id) => {
                writeln!(
                    f,
                    "{indent}Unary {op}",
                    indent = ctx.indent(),
                    op = op.kind.as_str()
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                writeln!(f, "{indent}Access", indent = ctx.indent())?;

                ctx.last = true;
                ctx.next_level();
                ctx.ast_print_expression(*expr_id, opts, f)?;
                writeln!(
                    f,
                    "{indent}ident={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier_ref(*ident_ref_id)
                )?;
                ctx.prev_level();
            }
            ExpressionKind::FunctionCall(expr_id, param_ids) => {
                writeln!(f, "{indent}Call", indent = ctx.indent())?;

                ctx.last = true;
                ctx.next_level();
                ctx.ast_print_expression(*expr_id, opts, f)?;

                if param_ids.is_empty() {
                    writeln!(f, "{indent}params=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}params", indent = ctx.indent())?;
                    ctx.last = true;
                    ctx.next_level();
                    for (i, param) in param_ids.iter().enumerate() {
                        ctx.last = i + 1 == param_ids.len();
                        ctx.ast_print_expression(*param, opts, f)?;
                    }
                    ctx.prev_level();
                }

                ctx.prev_level();
            }
            ExpressionKind::While(cond_id, expr_id) => {
                writeln!(f, "{indent}While", indent = ctx.indent())?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("cond");
                ctx.ast_print_expression(*cond_id, opts, f)?;
                ctx.tag = Some("body");
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;

                ctx.prev_level();
            }
            ExpressionKind::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    writeln!(f, "{indent}Block=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}Block", indent = ctx.indent())?;
                    ctx.last = true;
                    ctx.next_level();
                    for (i, stmt_id) in stmt_ids.iter().enumerate() {
                        ctx.last = i + 1 == stmt_ids.len();
                        ctx.ast_print_statement(*stmt_id, opts, f)?;
                    }
                    ctx.prev_level();
                }
            }
            ExpressionKind::StructInstantiation(ident_ref_id, generics, fields) => {
                writeln!(
                    f,
                    "{indent}StructInstantiate name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier_ref(*ident_ref_id)
                )?;

                ctx.last = true;
                ctx.next_level();
                if generics.is_empty() {
                    writeln!(f, "{indent}types=[]", indent = ctx.indent(),)?;
                } else {
                    writeln!(f, "{indent}types", indent = ctx.indent(),)?;
                    ctx.next_level();
                    for type_def_id in generics.iter() {
                        write!(f, "{indent}", indent = ctx.indent(),)?;
                        type_def_id.ast_print(ctx, opts, f)?;
                        writeln!(f)?;
                    }
                    ctx.prev_level();
                }
                ctx.prev_level();

                ctx.last = true;
                ctx.next_level();
                for (i, (field_ident, field_value)) in fields.iter().enumerate() {
                    writeln!(
                        f,
                        "{indent}field name={ident}",
                        indent = ctx.indent(),
                        ident = ctx.identifier_ref(*field_ident),
                    )?;
                    ctx.last = i + 1 == fields.len();
                    ctx.next_level();
                    ctx.last = true;
                    ctx.ast_print_expression(*field_value, opts, f)?;
                    ctx.prev_level();
                }
                ctx.prev_level();
            }
            ExpressionKind::ArrayInstantiation(values) => {
                writeln!(f, "{indent}ArrayInstantiate", indent = ctx.indent(),)?;
                ctx.last = true;
                ctx.next_level();
                for (i, expr_id) in values.iter().enumerate() {
                    ctx.last = i + 1 == values.len();
                    ctx.ast_print_expression(*expr_id, opts, f)?;
                }
                ctx.prev_level();
            }
            ExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => {
                writeln!(f, "{indent}ArrayAccess", indent = ctx.indent(),)?;

                ctx.last = true;
                ctx.next_level();
                ctx.ast_print_expression(*base_expr_id, opts, f)?;
                ctx.last = true;
                ctx.ast_print_expression(*index_expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::Dummy => unreachable!(),
        }
        ctx.prev_level();
        Ok(())
    }
}

impl AstPrint for Statement {
    fn ast_print<W>(
        &self,
        ctx: &mut AstPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        if let Some(tag) = ctx.tag.take() {
            writeln!(
                f,
                "{indent}{tag}:stmt {id}",
                indent = ctx.indent(),
                id = id!(self.id)
            )?;
        } else {
            writeln!(
                f,
                "{indent}stmt {id}",
                indent = ctx.indent(),
                id = id!(self.id)
            )?;
        }
        ctx.next_level();
        match &self.kind {
            StatementKind::Expression(expr_id) => {
                writeln!(f, "{indent}Expression", indent = ctx.indent(),)?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Namespace(ident, _, stmts) => {
                writeln!(
                    f,
                    "{indent}Namespace name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;

                ctx.last = true;
                ctx.next_level();
                if stmts.is_empty() {
                    writeln!(f, "{indent}stmts=[]", indent = ctx.indent(),)?;
                } else {
                    for (i, stmt) in stmts.iter().enumerate() {
                        ctx.last = i + 1 == stmts.len();
                        ctx.ast_print_statement(*stmt, opts, f)?;
                    }
                }
                ctx.prev_level();
            }
            StatementKind::Let(ident, expr_id) => {
                writeln!(
                    f,
                    "{indent}Let name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Ret(Some(expr_id), _mode) => {
                writeln!(f, "{indent}Ret", indent = ctx.indent())?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Ret(None, mode) => {
                writeln!(
                    f,
                    "{indent}Ret ({mode})",
                    indent = ctx.indent(),
                    mode = mode.as_str()
                )?;
            }
            StatementKind::LetFn(ident, annotations, parameters, ret_type, expr_id) => {
                writeln!(
                    f,
                    "{indent}Fn name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;
                ctx.last = true;
                ctx.next_level();

                if annotations.is_empty() {
                    writeln!(f, "{indent}annotations=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}annotations", indent = ctx.indent())?;
                    ctx.next_level();
                    for annotation in annotations {
                        writeln!(
                            f,
                            "{indent}{ident}",
                            indent = ctx.indent(),
                            ident = annotation
                                .ident_ref_ids
                                .iter()
                                .map(|ident_ref_id| ctx.identifier_ref(*ident_ref_id))
                                .collect::<Vec<_>>()
                                .join("."),
                        )?;
                    }
                    ctx.prev_level();
                }

                if parameters.is_empty() {
                    writeln!(f, "{indent}params=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}params", indent = ctx.indent())?;
                    ctx.next_level();
                    for parameter in parameters.iter() {
                        write!(
                            f,
                            "{indent}{ident}: ",
                            indent = ctx.indent(),
                            ident = ctx.identifier(parameter.identifier.id),
                        )?;
                        parameter.type_def_id.ast_print(ctx, opts, f)?;
                        writeln!(f)?;
                    }
                    ctx.prev_level();
                }

                if let Some(ret_type) = &ret_type.type_def_id {
                    write!(f, "{indent}ret=", indent = ctx.indent())?;
                    ret_type.ast_print(ctx, opts, f)?;
                    writeln!(f)?;
                } else {
                    writeln!(f, "{indent}ret=[]", indent = ctx.indent())?;
                }

                ctx.tag = Some("body");
                ctx.last = true;
                ctx.ast_print_expression(*expr_id, opts, f)?;

                ctx.prev_level();
            }
            StatementKind::Struct(ident, _annotations, type_parameters, fields) => {
                // todo use annotations
                writeln!(
                    f,
                    "{indent}Struct name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;

                ctx.last = true;
                ctx.next_level();
                if type_parameters.is_empty() {
                    writeln!(f, "{indent}types=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}types", indent = ctx.indent(),)?;
                    ctx.next_level();
                    for parameter in type_parameters.iter() {
                        writeln!(
                            f,
                            "{indent}{ident}",
                            indent = ctx.indent(),
                            ident = ctx.identifier(parameter.id),
                        )?;
                    }
                    ctx.prev_level();
                }
                ctx.prev_level();

                ctx.last = true;
                ctx.next_level();
                if fields.is_empty() {
                    writeln!(f, "{indent}fields=[]", indent = ctx.indent())?;
                } else {
                    for field in fields.iter() {
                        write!(
                            f,
                            "{indent}{ident}: ",
                            indent = ctx.indent(),
                            ident = ctx.identifier(field.identifier.id),
                        )?;
                        field.type_def_id.ast_print(ctx, opts, f)?;
                        writeln!(f)?;
                    }
                }
                ctx.prev_level();
            }
            StatementKind::Use(ident) => {
                writeln!(
                    f,
                    "{indent}Use {idents}",
                    indent = ctx.indent(),
                    idents = ident
                        .iter()
                        .map(|id| ctx.identifier_ref(*id))
                        .collect::<Vec<_>>()
                        .join(".")
                )?;
            }
            StatementKind::Annotation(ident) => {
                writeln!(
                    f,
                    "{indent}Annotation name={ident}",
                    indent = ctx.indent(),
                    ident = ctx.identifier(ident.id)
                )?;
            }
        }
        ctx.prev_level();
        Ok(())
    }
}

impl AstPrint for TypeDefId {
    fn ast_print<W>(
        &self,
        ctx: &mut AstPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        match &ctx.ast.type_defs[*self].kind {
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
                base.ast_print(ctx, opts, f)?;
                write!(f, "; {len}]")
            }
            TypeDefKind::Dummy => unreachable!(),
        }
    }
}

impl crate::Ast {
    pub fn ast_print<W>(&self, opts: &Options, f: &mut W) -> std::fmt::Result
    where
        W: Write,
    {
        let mut ctx = AstPrintContext {
            ast: self,
            indent: String::with_capacity(3 * 32),
            tag: None,
            last: true,
        };
        ctx.ast_print_statement(self.root, opts, f)?;
        Ok(())
    }
}

pub struct AstPrintContext<'a> {
    ast: &'a crate::Ast,
    indent: String,
    tag: Option<&'static str>,
    last: bool,
}

const NODE: &str = "+- ";
const INDENT: &str = "|  ";

// const NODE: &str = "";
// const INDENT: &str = "  ";

impl AstPrintContext<'_> {
    fn indent(&self) -> String {
        format!("{}{NODE}", self.indent)
    }

    fn next_level(&mut self) {
        if self.last {
            self.indent.push_str(&" ".repeat(INDENT.len()));
        } else {
            self.indent.push_str(INDENT);
        }
        self.last = false;
    }

    fn prev_level(&mut self) {
        for _ in 0..INDENT.len() {
            self.indent.pop();
        }
    }

    fn identifier(&self, ident_id: IdentId) -> &str {
        &self.ast.identifiers[ident_id]
    }

    fn identifier_ref(&self, ident_ref_id: IdentRefId) -> &str {
        self.identifier(self.ast.identifier_refs[ident_ref_id].ident.id)
    }

    fn ast_print_expression<W>(
        &mut self,
        expr_id: ExprId,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        self.ast.expressions[expr_id].ast_print(self, opts, f)
    }

    fn ast_print_statement<W>(
        &mut self,
        stmt_id: StmtId,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        self.ast.statements[stmt_id].ast_print(self, opts, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse;
    use insta::assert_snapshot;
    use transmute_core::input::Input;

    macro_rules! t {
        ($name:ident) => {
            #[test]
            fn $name() {
                let ast = parse(vec![Input::Internal(
                    "internal",
                    include_str!(concat!("../../examples/", stringify!($name), ".tm")),
                )])
                .1
                .unwrap();
                let mut s = String::new();
                ast.ast_print(&Options::default(), &mut s)
                    .expect("can print");
                assert_snapshot!(s);
            }
        };
    }

    t!(arrays_bounds);
    t!(arrays_if);
    t!(arrays_nested);
    t!(arrays_of_structs);
    t!(arrays_simple);
    t!(fibo_iter);
    t!(fibo_rec);
    t!(gc);
    t!(inner_function);
    t!(perimeter);
    t!(perimeter_lit_struct);
    t!(perimeter_var_struct);
    t!(print);
    t!(sibling_function);
    t!(string);
    t!(structs_anon);
    t!(structs_fn);
    t!(structs_inner);
    t!(structs_nested);
    t!(structs_of_arrays);
    t!(structs_simple);
    t!(structs_type_parameters);
    t!(void_fn);
}
