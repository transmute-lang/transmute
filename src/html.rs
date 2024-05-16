use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::{Parameter, RetMode, StatementKind};
use crate::ast::ResolvedAst;
use crate::resolver::{SymbolKind, Type};
use std::io;
use std::io::Write;
use xml::writer::XmlEvent;
use xml::{EmitterConfig, EventWriter};

const HTML: &str = include_str!("html/template.html");

struct HtmlWriter<'a> {
    ast: &'a ResolvedAst,
    par_id: usize,
    writer: EventWriter<Vec<u8>>,
}

macro_rules! make_html_symbol {
    ($name:ident, $class:expr, $text:expr) => {
        fn $name(&mut self) {
            self.emit(XmlEvent::start_element("span").attr("class", $class));
            self.emit(XmlEvent::Characters($text));
            self.emit(XmlEvent::end_element());
        }
    };
}

impl<'a> HtmlWriter<'a> {
    pub fn new(ast: &'a ResolvedAst) -> Self {
        let writer = EmitterConfig::new()
            .perform_indent(true)
            .write_document_declaration(false)
            .create_writer(vec![]);
        Self {
            ast,
            par_id: 0,
            writer,
        }
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(mut self) -> String {
        self.emit(XmlEvent::start_element("ul"));

        #[allow(clippy::unnecessary_to_owned)]
        for stmt in self.ast.statements().to_vec() {
            self.visit_statement(stmt);
        }

        self.emit(XmlEvent::end_element());

        let body = String::from_utf8(self.writer.into_inner()).unwrap();

        HTML.replace("{{body}}", &body)
    }

    fn visit_statement(&mut self, stmt: StmtId) {
        let stmt = self.ast.statement(stmt);

        match stmt.kind() {
            StatementKind::Expression(expr) => {
                self.emit(XmlEvent::start_element("li"));
                self.visit_expression(*expr);
                match self.ast.expression(*expr).kind() {
                    ExpressionKind::Assignment(_, _)
                    | ExpressionKind::Literal(_)
                    | ExpressionKind::Binary(_, _, _)
                    | ExpressionKind::Unary(_, _)
                    | ExpressionKind::FunctionCall(_, _) => {
                        self.emit_semicolon();
                    }
                    _ => {}
                }
                self.emit(XmlEvent::end_element());
            }
            StatementKind::Let(ident, expr) => {
                self.visit_let(stmt.id(), ident.id(), *expr);
            }
            StatementKind::Ret(expr, mode) => {
                self.visit_ret(*expr, *mode);
            }
            StatementKind::LetFn(ident, params, ret_type, expr) => self.visit_function(
                stmt.id(),
                ident.id(),
                params,
                ret_type.as_ref().map(|i| i.id()),
                *expr,
            ),
        }
    }

    fn visit_ret(&mut self, expr: ExprId, mode: RetMode) {
        self.emit(XmlEvent::start_element("li"));
        if let RetMode::Implicit = mode {
            self.emit(XmlEvent::start_element("span").attr("class", "implicit"));
        }

        self.emit_ret();
        if mode == RetMode::Implicit {
            self.emit(XmlEvent::end_element());
        }
        self.visit_expression(expr);
        self.emit_semicolon();
        self.emit(XmlEvent::end_element());
    }

    fn visit_function(
        &mut self,
        stmt_id: StmtId,
        ident: IdentId,
        params: &[Parameter],
        ret_type: Option<IdentId>,
        expr: ExprId,
    ) {
        self.emit(XmlEvent::start_element("li"));

        self.emit_let();
        self.emit_identifier(stmt_id, ident, None);

        let par_id = self.par_id();

        self.emit_par("(", &par_id);

        for (i, param) in params.iter().enumerate() {
            self.emit_identifier(stmt_id, param.identifier().id(), Some(i));
            self.emit_colon();
            // fixme should be an emit_identifier_ref
            self.emit_identifier(stmt_id, param.ty().id(), None);

            if i < params.len() - 1 {
                self.emit_comma();
            }
        }

        self.emit_par(")", &par_id);

        if let Some(ret_type) = ret_type {
            self.emit_colon();
            // fixme should be an emit_identifier_ref
            self.emit_identifier(stmt_id, ret_type, None);
        }

        self.emit_equal();

        let par_id = self.par_id();

        self.emit_curly("{", &par_id);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.visit_expression(expr);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.emit_curly("}", &par_id);
        self.emit(XmlEvent::end_element());
    }

    fn visit_let(&mut self, stmt: StmtId, ident: IdentId, expr: ExprId) {
        self.emit(XmlEvent::start_element("li"));
        self.emit_let();
        self.emit_identifier(stmt, ident, None);
        self.emit_equal();
        self.visit_expression(expr);
        self.emit_semicolon();
        self.emit(XmlEvent::end_element());
    }

    fn visit_expression(&mut self, expr: ExprId) {
        match self.ast.expression(expr).kind() {
            ExpressionKind::Assignment(ident_ref, expr) => self.visit_assignment(*ident_ref, *expr),
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(*cond, *true_branch, *false_branch)
            }
            ExpressionKind::Literal(lit) => self.visit_literal(lit),
            ExpressionKind::Binary(_left, _op, _right) => {
                unimplemented!("turned into functions during the resolution pass")
            }
            ExpressionKind::Unary(_, _) => {
                unimplemented!("turned into functions during the resolution pass")
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(*ident_ref, params)
            }
            ExpressionKind::While(cond, expr) => self.visit_while(*cond, *expr),
            ExpressionKind::Block(stmts) => self.visit_block(stmts),
            ExpressionKind::Dummy => unimplemented!("invalid source does not reach that point"),
        }
    }

    fn visit_assignment(&mut self, ident_ref: IdentRefId, expr: ExprId) {
        self.emit_identifier_ref(ident_ref);
        self.emit_equal();
        self.visit_expression(expr);
    }

    fn visit_if(&mut self, cond: ExprId, true_branch: ExprId, false_branch: Option<ExprId>) {
        // This is a bit tricky here: the <li> is already open in the visit_statement() function...
        // but the `if cond {` ends a line. Thus, we close the <li> tag after the `{`. But
        // as the visit_statement() expects to close one <li> as well, we leave the last one
        // open... This also works with `let a = if cond { ... } else { ... }`. In
        self.emit_if(self.ast.expression_type(true_branch));

        self.visit_expression(cond);

        let par_id = self.par_id();

        self.emit_curly("{", &par_id);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.visit_expression(true_branch);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.emit_curly("}", &par_id);

        if let Some(false_branch) = false_branch {
            self.emit(XmlEvent::end_element());
            self.emit(XmlEvent::start_element("li"));

            let par_id = self.par_id();

            self.emit_curly("{", &par_id);
            self.emit(XmlEvent::end_element());

            self.emit(XmlEvent::start_element("li"));
            self.visit_expression(false_branch);
            self.emit(XmlEvent::end_element());

            self.emit(XmlEvent::start_element("li"));
            self.emit_curly("}", &par_id);
        }
    }

    fn visit_literal(&mut self, literal: &Literal) {
        match literal.kind() {
            LiteralKind::Boolean(b) => self.emit_boolean(*b),
            LiteralKind::Identifier(ident) => self.emit_identifier_ref(*ident),
            LiteralKind::Number(n) => self.emit_number(*n),
        }
    }

    fn visit_function_call(&mut self, ident_ref: IdentRefId, params: &[ExprId]) {
        self.emit_identifier_ref(ident_ref);

        let par_id = self.par_id();
        self.emit_par("(", &par_id);

        for (i, param) in params.iter().enumerate() {
            self.visit_expression(*param);
            if i < params.len() - 1 {
                self.emit_comma();
            }
        }

        self.emit_par(")", &par_id);
    }

    fn visit_while(&mut self, cond: ExprId, expr: ExprId) {
        // see explanation on top of visit_id() function
        self.emit_while(self.ast.expression_type(expr));

        self.visit_expression(cond);

        let par_id = self.par_id();

        self.emit_curly("{", &par_id);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.visit_expression(expr);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("li"));
        self.emit_curly("}", &par_id);
    }

    fn visit_block(&mut self, stmts: &[StmtId]) {
        if !stmts.is_empty() {
            self.emit(XmlEvent::start_element("ul"));
            for stmt in stmts {
                self.visit_statement(*stmt);
            }
            self.emit(XmlEvent::end_element());
        }
    }

    fn emit<'e, E>(&mut self, event: E)
    where
        E: Into<XmlEvent<'e>>,
    {
        self.writer.write(event.into()).unwrap();
    }

    fn emit_if(&mut self, ty: &Type) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "kw")
                .attr("title", &ty.to_string()),
        );
        self.emit(XmlEvent::Characters("if"));
        self.emit(XmlEvent::end_element());
    }

    fn emit_while(&mut self, ty: &Type) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "kw")
                .attr("title", &ty.to_string()),
        );
        self.emit(XmlEvent::Characters("ret"));
        self.emit(XmlEvent::end_element());
    }

    fn emit_let(&mut self) {
        self.emit(XmlEvent::start_element("span").attr("class", "kw"));
        self.emit(XmlEvent::Characters("let"));
        self.emit(XmlEvent::end_element());
    }

    fn emit_ret(&mut self) {
        self.emit(XmlEvent::start_element("span").attr("class", "kw"));
        self.emit(XmlEvent::Characters("ret"));
        self.emit(XmlEvent::end_element());
    }

    fn emit_par(&mut self, symbol: &str, id: &str) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "par")
                .attr("data-par-id", id),
        );
        self.emit(XmlEvent::Characters(symbol));
        self.emit(XmlEvent::end_element());
    }

    fn emit_curly(&mut self, symbol: &str, id: &str) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "curly")
                .attr("data-par-id", id),
        );
        self.emit(XmlEvent::Characters(symbol));
        self.emit(XmlEvent::end_element());
    }

    make_html_symbol!(emit_comma, "comma", ", ");
    make_html_symbol!(emit_dot, "dot", ".");
    make_html_symbol!(emit_equal, "equal", " = ");
    make_html_symbol!(emit_colon, "colon", ": ");
    make_html_symbol!(emit_semicolon, "semicolon", ";");

    fn emit_boolean(&mut self, b: bool) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "boolean")
                .attr("title", &Type::Boolean.to_string()),
        );
        self.emit(XmlEvent::Characters(&format!("{}", b)));
        self.emit(XmlEvent::end_element());
    }

    fn emit_number(&mut self, n: i64) {
        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "num")
                .attr("title", &Type::Number.to_string()),
        );
        self.emit(XmlEvent::Characters(&format!("{}", n)));
        self.emit(XmlEvent::end_element());
    }

    fn ident_id(stmt: StmtId, index: Option<usize>) -> String {
        format!(
            "ident__stmt{}{}",
            stmt,
            index.map(|i| format!("_index{}", i)).unwrap_or_default()
        )
    }

    fn type_id(stmt: StmtId) -> String {
        format!("type__stmt{}", stmt)
    }

    fn par_id(&mut self) -> String {
        self.par_id += 1;
        format!("par_{}", self.par_id - 1)
    }

    fn emit_identifier(&mut self, stmt_id: StmtId, ident: IdentId, index: Option<usize>) {
        // todo tooltip with type
        self.emit(
            XmlEvent::start_element("span")
                .attr("id", &Self::ident_id(stmt_id, index))
                .attr("class", "ident"),
        );
        self.emit(XmlEvent::Characters(self.ast.identifier(ident)));
        self.emit(XmlEvent::end_element());
    }

    fn emit_identifier_ref(&mut self, identifier: IdentRefId) {
        let ident_ref = self.ast.identifier_ref(identifier);

        let type_name = self.ast.symbol(ident_ref.symbol_id()).ty().to_string();

        let type_ref = match self.ast.symbol(ident_ref.symbol_id()).ty() {
            Type::Boolean => "type__native_boolean",
            Type::Function => "type__function",
            Type::Number => "type__native_number",
            Type::Void => "type__native_void",
            Type::None => unimplemented!(),
        };

        let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
            SymbolKind::Let(stmt) => Self::ident_id(*stmt, None),
            SymbolKind::LetFn(stmt, _, _) => Self::ident_id(*stmt, None),
            SymbolKind::Parameter(stmt, index) => Self::ident_id(*stmt, Some(*index)),
            SymbolKind::Native(native) => {
                format!(
                    "ident__native_{}_{}_{}",
                    native.name(),
                    native
                        .parameters()
                        .iter()
                        .map(Type::to_string)
                        .collect::<Vec<String>>()
                        .join("_"),
                    native.return_type()
                )
            }
        };

        self.emit(
            XmlEvent::start_element("span")
                .attr("class", "ident_ref")
                .attr("title", &type_name)
                .attr("data-ident-ref", &symbol)
                .attr("data-type-ref", type_ref),
        );
        self.emit(XmlEvent::Characters(
            self.ast.identifier(ident_ref.ident().id()),
        ));
        self.emit(XmlEvent::end_element());
    }
}

#[cfg(test)]
mod tests {
    use crate::desugar::ImplicitRet;
    use crate::html::HtmlWriter;
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use insta::assert_snapshot;

    macro_rules! test_html_write {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let ast = Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRet::new())
                    .resolve(Resolver::new(), Natives::default())
                    .unwrap();

                let html = HtmlWriter::new(&ast).serialize();
                assert_snapshot!(&html);
            }
        };
    }

    test_html_write!(
        serialize_fibonacci_rec,
        r#"
            let f(n: number): number = {
                if n <= 1 {
                    ret n;
                }
                f(n - 1) + f(n - 2);
            }
        "#
    );

    test_html_write!(
        serialize_fibonacci_iter,
        r#"
            let f(n: number): number = {
                if n == 0 { ret 0; }
                if n == 1 { ret 1; }

                let prev_prev = 0;
                let prev = 1;
                let current = 0;

                let n = n;
                while n > 1 {
                    current = prev_prev + prev;
                    prev_prev = prev;
                    prev = current;
                    n = n - 1;
                }

                current;
            }
        "#
    );

    // test_html_write!(
    //     serialize_struct,
    //     r#"
    //         struct Point { x: number, y: number }
    //         let len(p: Point) = {
    //             p.x;
    //         }
    //     "#
    // );
    //
    // test_html_write!(
    //     serialize_nested_struct,
    //     r#"
    //         struct Point { x: number, y: number }
    //         struct Segment { from: Point, to: Point }
    //         let len(seg: Segment) = {
    //             seg.from.x;
    //         }
    //     "#
    // );
}
