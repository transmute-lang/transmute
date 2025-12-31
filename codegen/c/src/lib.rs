use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Write};
use transmute_codegen::mangling::{mangle_function_name, mangle_struct_name};
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, SymbolId, TypeId};
use transmute_mir::NativeFnKind;
use transmute_mir::{ExpressionKind, LiteralKind, Mir, StatementKind, SymbolKind, Target, Type};

struct Element {
    declaration: String,
    definition: String,
}

#[derive(Default)]
pub struct CCodegen {
    mangled_names: HashMap<SymbolId, String>,
    types: HashMap<TypeId, String>,
    includes: Vec<&'static str>,
    structs: Vec<Element>,
    functions: Vec<Element>,
}

macro_rules! unop {
    ($op:expr, $params:expr, $codegen:expr, $mir:expr, $w:expr) => {
        debug_assert_eq!($params.len(), 1);
        write!($w, "{op}", op = $op).unwrap();
        $codegen.gen_expression($mir, $params[0], $w);
    };
}

macro_rules! binop {
    ($op:expr, $params:expr, $codegen:expr, $mir:expr, $w:expr) => {
        debug_assert_eq!($params.len(), 2);
        $codegen.gen_expression($mir, $params[0], $w);
        write!($w, " {op} ", op = $op).unwrap();
        $codegen.gen_expression($mir, $params[1], $w);
    };
}

impl CCodegen {
    fn new() -> Self {
        Self::default()
    }

    fn codegen(&mut self, mir: &Mir) -> Result<CCode, Diagnostics<()>> {
        self.includes.push("#include <stdbool.h>\n");
        self.collect_struct_names(mir);
        self.collect_types(mir);
        self.gen_structs(mir);
        self.gen_functions(mir);

        let mut c_code = String::with_capacity(
            self.includes
                .iter()
                .fold(0, |acc, include| acc + include.len())
                + self
                    .structs
                    .iter()
                    .fold(0, |acc, e| acc + e.declaration.len() + e.definition.len())
                + self
                    .functions
                    .iter()
                    .fold(0, |acc, e| acc + e.declaration.len() + e.definition.len())
                + 512,
        );

        let all = self
            .includes
            .iter()
            .map(|i| i.as_ref())
            .chain(self.structs.iter().map(|s| s.declaration.as_str()))
            .chain(self.structs.iter().map(|s| s.definition.as_str()))
            .chain(self.functions.iter().map(|f| f.declaration.as_str()))
            .chain(self.functions.iter().map(|f| f.definition.as_str()));

        for s in all {
            c_code.push_str(s);
            c_code.push('\n');
        }

        Ok(CCode(c_code))
    }

    fn collect_types(&mut self, mir: &Mir) {
        for (type_id, ty) in mir.types.iter() {
            match &ty {
                Type::Boolean => {
                    self.types.insert(type_id, "bool".into());
                }
                Type::Number => {
                    self.types.insert(type_id, "double".into());
                }
                Type::Function(_, _) => {
                    // todo: implement
                }
                Type::Struct(sid, _) => {
                    self.types
                        .insert(type_id, format!("{}*", self.mangled_names[sid]));
                }
                Type::Array(_, _) => todo!(),
                Type::Void => {
                    self.types.insert(type_id, "void".into());
                }
                Type::None => {
                    // skip
                }
            }
        }
    }

    fn collect_struct_names(&mut self, mir: &Mir) {
        for (sid, s) in mir.structs.iter() {
            self.mangled_names.insert(
                s.symbol_id,
                format!(
                    "{}_{}",
                    mangle_struct_name(mir, sid, s.symbol_id),
                    s.symbol_id
                ),
            );
        }
    }

    fn gen_structs(&mut self, mir: &Mir) {
        self.structs.reserve(mir.structs.len());

        for (_, s) in mir.structs.iter() {
            let decl = format!("struct {name};\n", name = self.mangled_names[&s.symbol_id]);

            let mut def = "typedef struct ".to_string();
            if let Some(fields) = s.fields.as_ref()
                && fields.len() > 0
            {
                writeln!(&mut def, "{{").unwrap();
                for field in fields {
                    self.mangled_names.insert(
                        field.symbol_id,
                        format!(
                            "{}_{}",
                            &mir.identifiers[field.identifier.id], field.symbol_id
                        ),
                    );
                    writeln!(
                        &mut def,
                        "  {ty} {name};",
                        ty = self.types[&field.type_id],
                        name = self.mangled_names[&field.symbol_id]
                    )
                    .unwrap();
                }
                write!(&mut def, "}} ").unwrap();
            } else {
                write!(
                    &mut def,
                    "{mangled_name} ",
                    mangled_name = self.mangled_names[&s.symbol_id]
                )
                .unwrap();
            }
            writeln!(
                &mut def,
                "{mangled_name};",
                mangled_name = self.mangled_names[&s.symbol_id]
            )
            .unwrap();

            self.structs.push(Element {
                declaration: decl,
                definition: def,
            });
        }
    }

    fn gen_functions(&mut self, mir: &Mir) {
        self.functions.reserve(mir.functions.len());

        for (fid, f) in mir.functions.iter() {
            let parameters = f.parameters.iter().map(|p| p.type_id).collect::<Vec<_>>();
            self.mangled_names.insert(
                f.symbol_id,
                format!(
                    "{}_{}",
                    mangle_function_name(mir, f.identifier.id, &parameters, f.parent),
                    fid
                ),
            );
        }

        for (_, f) in mir.functions.iter() {
            let mut decl = String::new();
            write!(
                &mut decl,
                "{} {}(",
                self.types[&f.ret], self.mangled_names[&f.symbol_id]
            )
            .unwrap();
            if f.parameters.is_empty() {
                write!(&mut decl, "void").unwrap();
            } else {
                for (index, parameter) in f.parameters.iter().enumerate() {
                    self.mangled_names.insert(
                        parameter.symbol_id,
                        format!(
                            "{}_{}",
                            mir.identifiers[parameter.identifier.id], parameter.symbol_id
                        ),
                    );
                    write!(
                        &mut decl,
                        "{ty} {name}",
                        ty = self.types[&parameter.type_id],
                        name = self.mangled_names[&parameter.symbol_id]
                    )
                    .unwrap();
                    if index < f.parameters.len() - 1 {
                        write!(&mut decl, ", ").unwrap();
                    }
                }
            }
            write!(&mut decl, ")").unwrap();

            let mut def = Context::from(decl.clone());
            writeln!(&mut decl, ";").unwrap();
            writeln!(&mut def, "\n{{").unwrap();

            for (sid, var) in f.variables.iter() {
                self.mangled_names.insert(
                    *sid,
                    format!("{}_{sid}", mir.identifiers[var.identifier.id]),
                );
                writeln!(
                    &mut def,
                    "  {ty} {name};",
                    ty = self.types[&var.type_id],
                    name = self.mangled_names[sid]
                )
                .unwrap();
            }

            if let Some(body) = f.body {
                let (c, _) = self.gen_expression(mir, body, &mut def);
                def.write_str(c.as_str()).unwrap();
            }
            writeln!(&mut def, "}}").unwrap();

            self.functions.push(Element {
                declaration: decl,
                definition: def.into(),
            });
        }
    }

    fn gen_expression(&mut self, mir: &Mir, expr_id: ExprId, w: &mut Context) -> (Context, bool) {
        let mut c = Context::new_with_indent(w.indent, w.must_indent);

        let expr = &mir.expressions[expr_id];
        let need_semicolon = match &expr.kind {
            ExpressionKind::Assignment(Target::Direct(sid), expr) => {
                let (value, _need_semicolon) = self.gen_expression(mir, *expr, w);
                write!(w, "{name} = {value}", name = self.mangled_names[sid],).unwrap();
                // self.gen_expression(mir, *expr, w);
                true
            }
            ExpressionKind::Assignment(Target::Indirect(_), _) => todo!(),
            ExpressionKind::If(cond, true_expr_id, false_expr_id) => {
                write!(c, "if (").unwrap();
                self.gen_expression(mir, *cond, &mut c);
                writeln!(c, ") {{").unwrap();
                c.inc();
                self.gen_expression(mir, *true_expr_id, &mut c);
                c.dec();
                writeln!(c, "}}").unwrap();
                if let Some(false_expr_id) = false_expr_id {
                    writeln!(c, "else {{").unwrap();
                    c.inc();
                    self.gen_expression(mir, *false_expr_id, &mut c);
                    c.dec();
                    writeln!(c, "}}").unwrap();
                }
                false
            }
            ExpressionKind::Literal(lit) => {
                match &lit.kind {
                    LiteralKind::Boolean(bool) => {
                        write!(c, "{}", bool).unwrap();
                    }
                    LiteralKind::Identifier(sid) => {
                        write!(c, "{}", self.mangled_names[sid]).unwrap();
                    }
                    LiteralKind::Number(num) => {
                        write!(c, "{}", num).unwrap();
                    }
                    LiteralKind::String(_) => todo!(),
                }
                true
            }
            ExpressionKind::Access(_, _) => todo!(),
            ExpressionKind::FunctionCall(sid, parameters) => {
                let symbol = &mir.symbols[*sid];
                match &symbol.kind {
                    SymbolKind::LetFn(_, _) => {
                        write!(c, "{}(", self.mangled_names[sid]).unwrap();
                        for (index, expr_id) in parameters.iter().enumerate() {
                            self.gen_expression(mir, *expr_id, &mut c);
                            if index < parameters.len() - 1 {
                                write!(c, ", ").unwrap();
                            }
                        }
                        write!(c, ")").unwrap();
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::NegNumber) => {
                        unop!("-", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::AddNumberNumber) => {
                        binop!("+", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::SubNumberNumber) => {
                        binop!("-", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::MulNumberNumber) => {
                        binop!("*", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::DivNumberNumber) => {
                        binop!("/", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::EqNumberNumber)
                    | SymbolKind::Native(_, _, _, NativeFnKind::EqBooleanBoolean) => {
                        binop!("==", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::NeqNumberNumber)
                    | SymbolKind::Native(_, _, _, NativeFnKind::NeqBooleanBoolean) => {
                        binop!("!=", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::GtNumberNumber) => {
                        binop!(">", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::LtNumberNumber) => {
                        binop!("<", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::GeNumberNumber) => {
                        binop!(">=", &parameters, self, mir, &mut c);
                    }
                    SymbolKind::Native(_, _, _, NativeFnKind::LeNumberNumber) => {
                        binop!("<=", &parameters, self, mir, &mut c);
                    }
                    _ => unreachable!("can only call a function or an native"),
                }
                true
            }
            ExpressionKind::While(cond, body) => {
                write!(c, "while (").unwrap();
                self.gen_expression(mir, *cond, &mut c);
                writeln!(c, ") {{").unwrap();
                c.inc();
                self.gen_expression(mir, *body, &mut c);
                c.dec();
                writeln!(c, "}}").unwrap();
                false
            }
            ExpressionKind::Block(stmt_ids) => {
                c.inc();
                for stmt_id in stmt_ids {
                    match &mir.statements[*stmt_id].kind {
                        StatementKind::Expression(expr_id) => {
                            let (_, need_semicolon) = self.gen_expression(mir, *expr_id, &mut c);
                            if need_semicolon {
                                writeln!(c, ";").unwrap();
                            }
                        }
                        StatementKind::Ret(expr_id) => {
                            if let Some(expr_id) = expr_id {
                                write!(c, "return ").unwrap();
                                self.gen_expression(mir, *expr_id, &mut c);
                                writeln!(c, ";").unwrap();
                            } else {
                                writeln!(c, "return;").unwrap();
                            }
                        }
                    }
                }
                c.dec();
                false
            }
            ExpressionKind::StructInstantiation(sid, _struct_id, fields) => {
                writeln!(w, "x = malloc(sizeof({}));", self.mangled_names[sid],).unwrap();
                write!(c, "x").unwrap();

                for (_index, (_sid, _expr_id)) in fields.iter().enumerate() {}

                true
            }
            ExpressionKind::ArrayInstantiation(_) => todo!(),
            ExpressionKind::ArrayAccess(_, _) => todo!(),
        };

        (c, need_semicolon)
    }
}

struct Context {
    writer: String,
    indent: usize,
    must_indent: bool,
}

impl Context {
    fn new() -> Self {
        Self::new_with_indent(0, false)
    }

    fn new_with_indent(indent: usize, must_indent: bool) -> Self {
        Self {
            writer: String::new(),
            indent,
            must_indent,
        }
    }

    fn inc(&mut self) {
        self.indent += 1;
    }

    fn dec(&mut self) {
        self.indent -= 1;
    }

    fn as_str(&self) -> &str {
        &self.writer
    }
}

impl Write for Context {
    fn write_str(&mut self, s: &str) -> std::fmt::Result {
        if self.must_indent {
            for _ in 0..self.indent {
                self.writer.write_str("  ")?;
            }
        }
        self.must_indent = s.chars().last() == Some('\n');
        self.writer.write_str(s)
    }
}

impl Display for Context {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.writer)
    }
}

impl From<String> for Context {
    fn from(value: String) -> Self {
        Self {
            writer: value,
            indent: 0,
            must_indent: false,
        }
    }
}

impl From<Context> for String {
    fn from(value: Context) -> Self {
        value.writer
    }
}

pub struct CCode(String);

impl CCode {}

impl TryFrom<&Mir> for CCode {
    type Error = Diagnostics<()>;

    fn try_from(mir: &Mir) -> Result<Self, Self::Error> {
        CCodegen::new().codegen(mir)
    }
}

impl Display for CCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for CCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use transmute_ast::CompilationUnit;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_core::ids::InputId;
    use transmute_hir::Resolve;
    use transmute_nst::nodes::Nst;

    macro_rules! t {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit: CompilationUnit = Default::default();

                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), &format!("{}\nnamespace core {{}}", $src)),
                )
                .parse();

                let nst = Nst::from(compilation_unit.into_ast().unwrap());
                let hir = nst.resolve().unwrap();
                let mir = Mir::try_from(hir).unwrap();
                let c = CCode::try_from(&mir);
                assert_snapshot!(c.unwrap());
            }
        };
    }

    t!(struct_empty, "struct MyStruct {}");
    t!(struct_number_field, "struct MyStruct {field: number}");
    // t!(
    //     struct_instantiation,
    //     r#"
    //     struct MyStruct {field: number}
    //     let f() {
    //         let s = MyStruct {
    //             field: 1,
    //         };
    //     }
    // "#
    // );
    t!(function_empty, "let f() {}");
    t!(function_return_const_number, "let f(): number { 1; }");
    t!(function_return_const_boolean, "let f(): boolean { true; }");
    t!(function_with_parameter, "let f(n: number) { }");
    t!(function_with_parameters, "let f(n: number, o: boolean) { }");
    // todo: understand why the implicit return is left
    // todo: understand why we have a double indentation
    t!(op_minus, "let f() { -1; }");
    t!(
        fibonacci_rec,
        r#"
        let f(n: number): number {
            if n < 0 {
                ret n;
            }

            f(n - 2) + f(n - 1);
        }
    "#
    );
    t!(
        fibonacci_iter,
        r#"
        let f(n: number): number {
            if n < 2 { ret n; }

            let prev_prev = 0;
            let prev = 1;
            let current = 0;

            while n > 1 {
                current = prev_prev + prev;
                prev_prev = prev;
                prev = current;
                n = n - 1;
            }

            ret current;
        }
    "#
    );
}
