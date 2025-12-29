use crate::natives::Type;
use crate::nodes::{
    Expression, ExpressionKind, Implementation, Literal, LiteralKind, Statement, StatementKind,
    Target, TypeDefKind,
};
use crate::Hir;
use bimap::BiHashMap;
use std::fmt::Write;
use transmute_core::id;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, SymbolId, TypeDefId, TypeId};

pub trait HirPrint {
    fn hir_print<W>(
        &self,
        ctx: &mut HirPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write;
}

#[derive(Default)]
pub struct Options {}

impl HirPrint for Literal {
    fn hir_print<W>(
        &self,
        ctx: &mut HirPrintContext<'_>,
        _opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        match &self.kind {
            LiteralKind::Boolean(b) => {
                writeln!(
                    f,
                    "{indent}Bool: {b}",
                    indent = ctx.indent_type_id(ctx.resolve_type_id_by_type(Type::Boolean))
                )
            }
            LiteralKind::Identifier(ident) => {
                writeln!(
                    f,
                    "{indent}Ident: {ident}",
                    indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*ident)),
                    ident = ctx.identifier_ref_name(*ident),
                )
            }
            LiteralKind::Number(n) => {
                writeln!(
                    f,
                    "{indent}Number: {n}",
                    indent = ctx.indent_type_id(ctx.resolve_type_id_by_type(Type::Number))
                )
            }
            LiteralKind::String(n) => {
                // todo type
                writeln!(f, "{indent}String: {n}", indent = ctx.indent())
            }
        }
    }
}

impl HirPrint for Expression {
    fn hir_print<W>(
        &self,
        ctx: &mut HirPrintContext<'_>,
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
                indent = ctx.indent_type_id(self.resolved_type_id()),
                id = id!(self.id)
            )?;
        } else {
            writeln!(
                f,
                "{indent}expr {id}",
                indent = ctx.indent_type_id(self.resolved_type_id()),
                id = id!(self.id)
            )?;
        }

        ctx.next_level();
        match &self.kind {
            ExpressionKind::Assignment(Target::Direct(target), expr_id) => {
                writeln!(
                    f,
                    "{indent}Assignment target={ident}",
                    indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*target)),
                    ident = ctx.identifier_ref_name(*target)
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.hir_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                writeln!(
                    f,
                    "{indent}Assignment",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                )?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("target");
                ctx.hir_print_expression(*lhs_expr_id, opts, f)?;
                ctx.tag = Some("value");
                ctx.last = true;
                ctx.hir_print_expression(*rhs_expr_id, opts, f)?;
                ctx.prev_level();
            }
            ExpressionKind::If(cond_id, true_id, false_id) => {
                writeln!(
                    f,
                    "{indent}If",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                )?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("cond");
                ctx.hir_print_expression(*cond_id, opts, f)?;

                ctx.tag = Some("true");
                ctx.last = !false_id.is_some();
                ctx.hir_print_expression(*true_id, opts, f)?;

                if let Some(false_id) = false_id {
                    ctx.tag = Some("false");
                    ctx.last = true;
                    ctx.hir_print_expression(*false_id, opts, f)?;
                }

                ctx.prev_level();
            }
            ExpressionKind::Literal(lit) => lit.hir_print(ctx, opts, f)?,
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                writeln!(
                    f,
                    "{indent}Access",
                    indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*ident_ref_id))
                )?;

                ctx.last = true;
                ctx.next_level();
                ctx.tag = Some("lhs");
                ctx.hir_print_expression(*expr_id, opts, f)?;
                writeln!(
                    f,
                    "{indent}ident={ident}",
                    indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*ident_ref_id)),
                    ident = ctx.identifier_ref_name(*ident_ref_id)
                )?;
                ctx.prev_level();
            }
            ExpressionKind::FunctionCall(expr_id, param_ids) => {
                writeln!(
                    f,
                    "{indent}Call",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                )?;

                ctx.last = true;
                ctx.next_level();
                ctx.tag = Some("callee");
                ctx.hir_print_expression(*expr_id, opts, f)?;

                if param_ids.is_empty() {
                    writeln!(f, "{indent}params=[]", indent = ctx.indent())?;
                } else {
                    writeln!(f, "{indent}params", indent = ctx.indent())?;
                    ctx.last = true;
                    ctx.next_level();
                    for (i, param) in param_ids.iter().enumerate() {
                        ctx.last = i + 1 == param_ids.len();
                        ctx.hir_print_expression(*param, opts, f)?;
                    }
                    ctx.prev_level();
                }

                ctx.prev_level();
            }
            ExpressionKind::While(cond_id, expr_id) => {
                writeln!(
                    f,
                    "{indent}While",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                )?;
                ctx.last = true;
                ctx.next_level();

                ctx.tag = Some("cond");
                ctx.hir_print_expression(*cond_id, opts, f)?;
                ctx.tag = Some("body");
                ctx.last = true;
                ctx.hir_print_expression(*expr_id, opts, f)?;

                ctx.prev_level();
            }
            ExpressionKind::Block(stmt_ids) => {
                if stmt_ids.is_empty() {
                    writeln!(
                        f,
                        "{indent}Block=[]",
                        indent =
                            ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                    )?;
                } else {
                    writeln!(
                        f,
                        "{indent}Block",
                        indent =
                            ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id())
                    )?;
                    ctx.last = true;
                    ctx.next_level();
                    for (i, stmt_id) in stmt_ids.iter().enumerate() {
                        ctx.last = i + 1 == stmt_ids.len();
                        ctx.hir_print_statement(*stmt_id, opts, f)?;
                    }
                    ctx.prev_level();
                }
            }
            ExpressionKind::StructInstantiation(ident_ref_id, _, fields) => {
                writeln!(
                    f,
                    "{indent}StructInstantiate name={ident}",
                    indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*ident_ref_id)),
                    ident = ctx.identifier_ref_name(*ident_ref_id)
                )?;
                ctx.last = true;
                ctx.next_level();
                for (i, (field_ident, field_value)) in fields.iter().enumerate() {
                    writeln!(
                        f,
                        "{indent}field name={ident}",
                        indent = ctx.indent_symbol_ref(ctx.identifier_ref_symbol(*field_ident)),
                        ident = ctx.identifier_ref_name(*field_ident),
                    )?;
                    ctx.last = i + 1 == fields.len();
                    ctx.next_level();
                    ctx.last = true;
                    ctx.hir_print_expression(*field_value, opts, f)?;
                    ctx.prev_level();
                }
                ctx.prev_level();
            }
            ExpressionKind::ArrayInstantiation(values) => {
                writeln!(
                    f,
                    "{indent}ArrayInstantiate",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id()),
                )?;
                ctx.last = true;
                ctx.next_level();
                for (i, expr_id) in values.iter().enumerate() {
                    ctx.last = i + 1 == values.len();
                    ctx.hir_print_expression(*expr_id, opts, f)?;
                }
                ctx.prev_level();
            }
            ExpressionKind::ArrayAccess(base_expr_id, index_expr_id) => {
                writeln!(
                    f,
                    "{indent}ArrayAccess",
                    indent = ctx.indent_type_id(ctx.hir.expressions[self.id].resolved_type_id()),
                )?;

                ctx.last = true;
                ctx.next_level();
                ctx.hir_print_expression(*base_expr_id, opts, f)?;
                ctx.last = true;
                ctx.hir_print_expression(*index_expr_id, opts, f)?;
                ctx.prev_level();
            }
        }
        ctx.prev_level();
        Ok(())
    }
}

impl HirPrint for Statement {
    fn hir_print<W>(
        &self,
        ctx: &mut HirPrintContext<'_>,
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
                writeln!(
                    f,
                    "{indent}Expression",
                    indent = ctx.indent_type_id(ctx.hir.expressions[*expr_id].resolved_type_id()),
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.hir_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Namespace(ident, _, stmts) => {
                writeln!(
                    f,
                    "{indent}Namespace name={ident}",
                    indent = ctx.indent_symbol_def(ident.resolved_symbol_id()),
                    ident = ctx.identifier(ident.id)
                )?;

                ctx.last = true;
                ctx.next_level();
                if stmts.is_empty() {
                    writeln!(f, "{indent}stmts=[]", indent = ctx.indent(),)?;
                } else {
                    for (i, stmt) in stmts.iter().enumerate() {
                        ctx.last = i + 1 == stmts.len();
                        ctx.hir_print_statement(*stmt, opts, f)?;
                    }
                }
                ctx.prev_level();
            }
            StatementKind::Let(ident, expr_id) => {
                writeln!(
                    f,
                    "{indent}Let name={ident}",
                    indent = ctx.indent_symbol_def(ident.resolved_symbol_id()),
                    ident = ctx.identifier(ident.id)
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.hir_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Ret(Some(expr_id), _mode) => {
                writeln!(
                    f,
                    "{indent}Ret",
                    indent = ctx.indent_type_id(ctx.hir.expressions[*expr_id].resolved_type_id())
                )?;
                ctx.last = true;
                ctx.next_level();
                ctx.last = true;
                ctx.hir_print_expression(*expr_id, opts, f)?;
                ctx.prev_level();
            }
            StatementKind::Ret(None, mode) => {
                writeln!(
                    f,
                    "{indent}Ret ({mode})",
                    indent = ctx.indent_type_id(ctx.resolve_type_id_by_type(Type::Void)),
                    mode = mode.as_str()
                )?;
            }
            StatementKind::LetFn(ident, annotations, parameters, ret_type, expr_id, fn_stmt_id) => {
                writeln!(
                    f,
                    "{indent}Fn name={ident}{native}{fn_stmt_id}",
                    indent = ctx.indent_symbol_def(ident.resolved_symbol_id()),
                    ident = ctx.identifier(ident.id),
                    native = match expr_id {
                        Implementation::Provided(_) => "",
                        _ => " (native)",
                    },
                    fn_stmt_id = fn_stmt_id
                        .map(|id| format!(", fn_stmt_id={id}"))
                        .unwrap_or_default()
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
                            indent =
                                ctx.indent_symbol_ref(ctx.identifier_ref_symbol(
                                    *annotation.ident_ref_ids.last().unwrap()
                                )),
                            ident = annotation
                                .ident_ref_ids
                                .iter()
                                .map(|ident_ref_id| ctx.identifier_ref_name(*ident_ref_id))
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
                            indent = ctx.indent_symbol_def(parameter.resolved_symbol_id()),
                            ident = ctx.identifier(parameter.identifier.id),
                        )?;
                        parameter.type_def_id.hir_print(ctx, opts, f)?;
                        writeln!(f)?;
                    }
                    ctx.prev_level();
                }

                if let Some(ret_type) = &ret_type.type_def_id {
                    write!(
                        f,
                        "{indent}ret=",
                        indent = ctx.indent_type_id(ctx.resolve_type_id_by_type_def_id(*ret_type))
                    )?;
                    ret_type.hir_print(ctx, opts, f)?;
                    writeln!(f)?;
                } else {
                    writeln!(
                        f,
                        "{indent}ret=[]",
                        indent = ctx.indent_type_id(ctx.resolve_type_id_by_type(Type::Void))
                    )?;
                }

                if let Implementation::Provided(expr_id) = expr_id {
                    ctx.tag = Some("body");
                    ctx.last = true;
                    ctx.hir_print_expression(*expr_id, opts, f)?;
                }

                ctx.prev_level();
            }
            StatementKind::Struct(ident, _annotations, fields, _, fn_stmt_id) => {
                // todo use annotations
                writeln!(
                    f,
                    "{indent}Struct name={ident}{native}{fn_stmt_id}",
                    indent = ctx.indent_symbol_def(ident.resolved_symbol_id()),
                    ident = ctx.identifier(ident.id),
                    native = match fields {
                        Implementation::Provided(_) => "",
                        _ => " (native)",
                    },
                    fn_stmt_id = fn_stmt_id
                        .map(|id| format!(", fn_stmt_id={id}"))
                        .unwrap_or_default()
                )?;
                ctx.last = true;
                ctx.next_level();

                if let Implementation::Provided(fields) = fields {
                    if fields.is_empty() {
                        writeln!(f, "{indent}fields=[]", indent = ctx.indent())?;
                    } else {
                        for field in fields.iter() {
                            write!(
                                f,
                                "{indent}{ident}: ",
                                indent = ctx.indent_symbol_def(field.resolved_symbol_id()),
                                ident = ctx.identifier(field.identifier.id),
                            )?;
                            field.type_def_id.hir_print(ctx, opts, f)?;
                            writeln!(f)?;
                        }
                    }
                }
                ctx.prev_level();
            }
            StatementKind::Use(_) => {
                unreachable!("for as long as the resolver removes the use statements")
            }
            StatementKind::Annotation(ident) => {
                writeln!(
                    f,
                    "{indent}Annotation name={ident}",
                    indent = ctx.indent_symbol_def(ident.resolved_symbol_id()),
                    ident = ctx.identifier(ident.id)
                )?;
            }
        }
        ctx.prev_level();
        Ok(())
    }
}

impl HirPrint for TypeDefId {
    fn hir_print<W>(
        &self,
        ctx: &mut HirPrintContext<'_>,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        match &ctx.hir.type_defs[*self].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                write!(
                    f,
                    "{}",
                    ident_ref_ids
                        .iter()
                        .map(|ident_ref| ctx.identifier_ref_name(*ident_ref))
                        .collect::<Vec<_>>()
                        .join(".")
                )
            }
            TypeDefKind::Array(base, len) => {
                write!(f, "[")?;
                base.hir_print(ctx, opts, f)?;
                write!(f, "; {len}]")
            }
        }
    }
}

impl Hir {
    pub fn hir_print<W>(&self, opts: &Options, f: &mut W) -> std::fmt::Result
    where
        W: Write,
    {
        writeln!(f, "   sym    typ")?;
        let types = self.types.iter().collect::<BiHashMap<_, _>>();

        let mut ctx = HirPrintContext {
            hir: self,
            types,
            indent: String::with_capacity(3 * 32),
            tag: None,
            last: true,
        };
        ctx.hir_print_statement(self.root, opts, f)?;
        writeln!(f, "\n--- types ---")?;
        for (id, ty) in &ctx.hir.types {
            write!(f, "{id:-5}: ")?;
            self.print_type(f, ty)?;
            writeln!(f,)?;
        }
        Ok(())
    }

    fn print_type<W>(&self, f: &mut W, ty: &Type) -> std::fmt::Result
    where
        W: Write,
    {
        match ty {
            Type::Invalid => write!(f, "invalid"),
            Type::Boolean => write!(f, "boolean"),
            Type::Number => write!(f, "number"),
            Type::Function(params, ret) => {
                write!(f, "f(")?;
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", id!(*param))?;
                }
                write!(f, ") : {}", id!(*ret))
            }
            Type::Struct(stmt_id, type_parameters) => {
                let symbol_id = match &self.statements[*stmt_id].kind {
                    StatementKind::Struct(ident, _, _, _, _) => ident.resolved_symbol_id(),
                    _ => panic!("struct expected"),
                };
                write!(f, "struct {}<{}>", id!(symbol_id), type_parameters.len())
            }
            Type::Array(type_id, size) => {
                write!(f, "[{type_id}; {size}]", type_id = id!(*type_id))
            }
            Type::Parameter(stmt_id, index) => {
                let symbol_id = match &self.statements[*stmt_id].kind {
                    StatementKind::Struct(ident, _, _, _, _) => ident.resolved_symbol_id(),
                    _ => panic!("struct expected"),
                };
                write!(f, "type parameter {symbol_id}<{stmt_id}.{index}>")
            }
            Type::Type => write!(f, "type"),
            Type::Void => write!(f, "void"),
            Type::None => write!(f, "none"),
        }
    }
}

pub struct HirPrintContext<'a> {
    hir: &'a Hir,
    types: BiHashMap<TypeId, &'a Type>,
    indent: String,
    tag: Option<&'static str>,
    last: bool,
}

const NODE: &str = "+- ";
const INDENT: &str = "|  ";

// const NODE: &str = "";
// const INDENT: &str = "  ";

impl HirPrintContext<'_> {
    fn indent(&self) -> String {
        format!("               {}{NODE}", self.indent)
    }

    fn indent_symbol_def(&self, symbol_id: SymbolId) -> String {
        format!(
            "={symbol_id:-5}: {type_id:-5}  {}{NODE}",
            self.indent,
            symbol_id = id!(symbol_id),
            type_id = id!(self.hir.symbols[symbol_id].type_id),
        )
    }

    fn indent_symbol_ref(&self, symbol_id: SymbolId) -> String {
        format!(
            "@{symbol_id:-5}: {type_id:-5}  {}{NODE}",
            self.indent,
            symbol_id = id!(symbol_id),
            type_id = id!(self.hir.symbols[symbol_id].type_id),
        )
    }

    fn resolve_type_id_by_type_def_id(&self, type_def_id: TypeDefId) -> TypeId {
        match &self.hir.type_defs[type_def_id].kind {
            TypeDefKind::Simple(ident_ref_ids) => {
                self.hir.symbols[self.identifier_ref_symbol(*ident_ref_ids.last().unwrap())].type_id
            }
            TypeDefKind::Array(type_def_id_inner, size) => {
                let ty = Type::Array(
                    self.resolve_type_id_by_type_def_id(*type_def_id_inner),
                    *size,
                );
                self.resolve_type_id_by_type(ty)
            }
        }
    }

    fn resolve_type_id_by_type(&self, ty: Type) -> TypeId {
        *self.types.get_by_right(&ty).unwrap()
    }

    fn indent_type_id(&self, type_id: TypeId) -> String {
        format!(
            "@     : {type_id:-5}  {}{NODE}",
            self.indent,
            type_id = id!(type_id),
        )
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
        &self.hir.identifiers[ident_id]
    }

    fn identifier_ref_name(&self, ident_ref_id: IdentRefId) -> &str {
        self.identifier(self.hir.identifier_refs[ident_ref_id].ident.id)
    }

    fn identifier_ref_symbol(&self, ident_ref_id: IdentRefId) -> SymbolId {
        self.hir.identifier_refs[ident_ref_id].resolved_symbol_id()
    }

    fn hir_print_expression<W>(
        &mut self,
        expr_id: ExprId,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        self.hir.expressions[expr_id].hir_print(self, opts, f)
    }

    fn hir_print_statement<W>(
        &mut self,
        stmt_id: StmtId,
        opts: &Options,
        f: &mut W,
    ) -> std::fmt::Result
    where
        W: Write,
    {
        self.hir.statements[stmt_id].hir_print(self, opts, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Natives;
    use insta::assert_snapshot;
    use std::env;
    use std::path::PathBuf;
    use transmute_ast::parse;
    use transmute_core::input::Input;
    use transmute_nst::nodes::Nst;

    macro_rules! t {
        ($name:ident) => {
            #[test]
            fn $name() {
                let stdlib_path = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap())
                    .parent()
                    .unwrap()
                    .join("stdlib")
                    .join("src")
                    .join("stdlib.tm");

                let inputs = vec![
                    Input::core(),
                    Input::from((
                        "test",
                        include_str!(concat!("../../examples/", stringify!($name), ".tm")),
                    )),
                    Input::try_from(stdlib_path).unwrap(),
                ];

                let ast = parse(inputs).1.unwrap();
                let nst = Nst::from(ast);
                let hir = crate::Resolver::new().resolve(Natives::new(), nst).unwrap();

                let mut s = String::new();
                hir.hir_print(&Options::default(), &mut s)
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
