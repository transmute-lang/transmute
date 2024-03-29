use crate::ast::expression::{Expression, ExpressionKind};
use crate::ast::identifier::Identifier;
use crate::ast::ids::{ExprId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::{Parameter, Statement, StatementKind};
use crate::ast::Ast;
use crate::resolver::Symbol;
use std::io;
use std::io::Write;
use xml::writer::XmlEvent;
use xml::{EmitterConfig, EventWriter};

pub struct XmlWriter<'a> {
    ast: &'a Ast,
    symbols: &'a Vec<Symbol>,
    writer: EventWriter<Vec<u8>>,
}

impl<'a> XmlWriter<'a> {
    pub fn new(ast: &'a Ast, symbols: &'a Vec<Symbol>) -> Self {
        let writer = EmitterConfig::new()
            .perform_indent(true)
            .create_writer(vec![]);
        Self {
            ast,
            symbols,
            writer,
        }
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(mut self) -> String {
        // todo review ref, ident-ref, type-ref, target-id in ast

        self.emit(XmlEvent::start_element("unit"));

        self.emit(XmlEvent::start_element("ast"));

        self.emit(XmlEvent::start_element("identifiers"));
        for (id, identifier) in self.ast.identifiers().iter().enumerate() {
            self.emit(XmlEvent::start_element("ident").attr("id", &format!("ident:{id}")));
            self.emit(XmlEvent::Characters(identifier));
            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        #[allow(clippy::unnecessary_to_owned)]
        for stmt in self.ast.statements().to_vec() {
            self.visit_statement(stmt);
        }
        self.emit(XmlEvent::end_element()); // ast

        self.emit(XmlEvent::end_element()); // unit

        String::from_utf8(self.writer.into_inner()).unwrap()
    }

    fn emit<'e, E>(&mut self, event: E)
    where
        E: Into<XmlEvent<'e>>,
    {
        self.writer.write(event.into()).unwrap();
    }

    fn visit_statement(&mut self, stmt: StmtId) {
        let stmt = self.ast.statement(stmt);
        let id = stmt.id().to_string();

        self.emit(
            XmlEvent::start_element("stmt")
                .attr("id", &format!("stmt:{id}"))
                .attr("line", &stmt.span().line().to_string())
                .attr("column", &stmt.span().column().to_string())
                .attr("start", &stmt.span().start().to_string())
                .attr("len", &stmt.span().len().to_string()),
        );

        match stmt.kind() {
            StatementKind::Expression(expr) => {
                self.visit_expression(*expr);
            }
            StatementKind::Let(ident, expr) => {
                self.visit_let(ident, expr);
            }
            StatementKind::Ret(expr) => {
                self.visit_ret(stmt, expr);
            }
            StatementKind::LetFn(ident, params, ty, expr) => {
                self.visit_function(stmt.id(), ident, params, ty, expr);
            }
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_expression(&mut self, expr: ExprId) {
        let expr = self.ast.expression(expr);

        self.emit(
            XmlEvent::start_element("expr")
                .attr("id", &format!("expr:{}", expr.id()))
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string()),
        );

        match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                self.visit_assignment(ident_ref, expr);
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(cond, true_branch, false_branch);
            }
            ExpressionKind::Literal(literal) => self.visit_literal(literal),
            ExpressionKind::Binary(left, op, right) => {
                self.visit_binary_operator(expr, left, op, right);
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(expr, ident_ref, params);
            }
            ExpressionKind::Unary(op, expr) => {
                self.visit_unary_operator(op, expr);
            }
            ExpressionKind::While(cond, expr) => {
                self.visit_while(cond, expr);
            }
            ExpressionKind::Block(stmts) => {
                self.visit_block(stmts);
            }
            ExpressionKind::Dummy => {}
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_assignment(&mut self, ident_ref: &IdentRefId, expr: &ExprId) {
        let ident_ref = self.ast.identifier_ref(*ident_ref);

        let symbol = ident_ref
            .symbol_id()
            .map(|sid| &self.symbols[sid.id()])
            .map(|s| match s.kind() {
                crate::resolver::SymbolKind::Let(stmt) => {
                    format!("stmt:{stmt}")
                }
                crate::resolver::SymbolKind::LetFn(stmt, _, _) => {
                    format!("stmt:{stmt}")
                }
                crate::resolver::SymbolKind::Parameter(stmt, index) => {
                    format!("stmt:{}:{}", stmt.id(), index)
                }
                crate::resolver::SymbolKind::Native(_) => "native".to_string(),
            })
            .expect("assignment identifier not found");

        self.emit(
            XmlEvent::start_element("assign")
                .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                .attr("target-id", &symbol),
        );

        self.emit(XmlEvent::start_element("identifier"));
        self.emit(XmlEvent::characters(
            self.ast.identifier(ident_ref.ident().id()),
        ));
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("expression"));
        self.visit_expression(*expr);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }

    fn visit_if(&mut self, cond: &ExprId, true_branch: &ExprId, false_branch: &Option<ExprId>) {
        self.emit(XmlEvent::start_element("if"));

        self.emit(XmlEvent::start_element("condition"));
        self.visit_expression(*cond);
        self.emit(XmlEvent::end_element());

        let true_branch = self.ast.expression(*true_branch);
        self.emit(XmlEvent::start_element("true"));
        self.visit_expression(true_branch.id());
        self.emit(XmlEvent::end_element());

        if let Some(false_branch) = false_branch {
            let false_branch = self.ast.expression(*false_branch);
            self.emit(XmlEvent::start_element("false"));
            self.visit_expression(false_branch.id());
            self.emit(XmlEvent::end_element());
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_literal(&mut self, literal: &Literal) {
        match literal.kind() {
            LiteralKind::Boolean(b) => {
                self.emit(XmlEvent::start_element("bool"));
                self.emit(XmlEvent::characters(&b.to_string()));
                self.emit(XmlEvent::end_element());
            }
            LiteralKind::Identifier(ident_ref) => {
                let ident_ref = self.ast.identifier_ref(*ident_ref);

                let symbol = ident_ref
                    .symbol_id()
                    .map(|sid| &self.symbols[sid.id()])
                    .map(|s| match s.kind() {
                        crate::resolver::SymbolKind::Let(stmt) => {
                            format!("stmt:{stmt}")
                        }
                        crate::resolver::SymbolKind::LetFn(stmt, _, _) => {
                            format!("stmt:{stmt}")
                        }
                        crate::resolver::SymbolKind::Parameter(stmt, index) => {
                            format!("stmt:{}:{}", stmt.id(), index)
                        }
                        crate::resolver::SymbolKind::Native(_) => "native".to_string(),
                    })
                    .expect("literal identifier not found");

                self.emit(
                    XmlEvent::start_element("identifier-ref")
                        .attr("id", &format!("ident-ref:{}", ident_ref.id()))
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        .attr("target-id", &symbol),
                );
                self.emit(XmlEvent::characters(
                    self.ast.identifier(ident_ref.ident().id()),
                ));
                self.emit(XmlEvent::end_element());
            }
            LiteralKind::Number(number) => {
                self.emit(XmlEvent::start_element("number"));
                self.emit(XmlEvent::characters(&number.to_string()));
                self.emit(XmlEvent::end_element());
            }
        }
    }

    fn visit_binary_operator(
        &mut self,
        expr: &Expression,
        left: &ExprId,
        op: &BinaryOperator,
        right: &ExprId,
    ) {
        self.emit(
            XmlEvent::start_element("binary")
                .attr("operator", &op.kind().to_string())
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string()),
        );

        self.emit(XmlEvent::start_element("left"));
        self.visit_expression(*left);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("right"));
        self.visit_expression(*right);
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }

    fn visit_function_call(
        &mut self,
        expr: &Expression,
        ident_ref: &IdentRefId,
        params: &[ExprId],
    ) {
        let ident_ref = self.ast.identifier_ref(*ident_ref);

        let symbol = ident_ref
            .symbol_id()
            .map(|sid| &self.symbols[sid.id()])
            .map(|s| match s.kind() {
                crate::resolver::SymbolKind::Let(stmt) => {
                    format!("stmt:{stmt}")
                }
                crate::resolver::SymbolKind::LetFn(stmt, _, _) => {
                    format!("stmt:{stmt}")
                }
                crate::resolver::SymbolKind::Parameter(stmt, index) => {
                    let param = match self.ast.statement(*stmt).kind() {
                        StatementKind::LetFn(_, params, _, _) => &params[*index],
                        _ => panic!(),
                    };
                    format!("ident:{}", param.identifier().id())
                }
                crate::resolver::SymbolKind::Native(native) => {
                    format!(
                        "native:{}:{}:{}",
                        native.name(),
                        native
                            .parameters()
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<String>>()
                            .join(":"),
                        native.return_type()
                    )
                }
            })
            .expect("function identifier not found");

        self.emit(
            XmlEvent::start_element("call")
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string())
                .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                .attr("name", self.ast.identifier(ident_ref.ident().id()))
                .attr("target-id", &symbol),
        );

        if !params.is_empty() {
            self.emit(XmlEvent::start_element("parameters"));
            #[allow(clippy::unnecessary_to_owned)]
            for param in params.to_vec() {
                self.emit(XmlEvent::start_element("parameter"));
                self.visit_expression(param);
                self.emit(XmlEvent::end_element());
            }
            self.emit(XmlEvent::end_element());
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_unary_operator(&mut self, op: &UnaryOperator, expr: &ExprId) {
        self.emit(XmlEvent::start_element("unary").attr("operator", &op.kind().to_string()));

        self.visit_expression(*expr);

        self.emit(XmlEvent::end_element());
    }

    fn visit_while(&mut self, cond: &ExprId, expr: &ExprId) {
        self.emit(XmlEvent::start_element("while"));

        let cond = self.ast.expression(*cond);
        self.emit(
            XmlEvent::start_element("condition")
                .attr("line", &cond.span().line().to_string())
                .attr("column", &cond.span().column().to_string())
                .attr("start", &cond.span().start().to_string())
                .attr("len", &cond.span().len().to_string()),
        );
        self.visit_expression(cond.id());
        self.emit(XmlEvent::end_element());

        let expr = self.ast.expression(*expr);
        self.emit(XmlEvent::start_element("body"));
        self.visit_expression(expr.id());
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }

    fn visit_block(&mut self, stmts: &[StmtId]) {
        self.emit(XmlEvent::start_element("block"));

        #[allow(clippy::unnecessary_to_owned)]
        for stmt in stmts.to_vec() {
            self.visit_statement(stmt);
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_let(&mut self, ident: &Identifier, expr: &ExprId) {
        self.emit(XmlEvent::start_element("let"));

        self.emit(
            XmlEvent::start_element("identifier")
                .attr("ref", &format!("ident:{}", ident.id()))
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(self.ast.identifier(ident.id())));
        self.emit(XmlEvent::end_element());

        let expr = self.ast.expression(*expr);

        self.emit(
            XmlEvent::start_element("expression")
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string()),
        );
        self.visit_expression(expr.id());
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }

    fn visit_ret(&mut self, stmt: &Statement, expr: &ExprId) {
        self.emit(
            XmlEvent::start_element("ret")
                .attr("line", &stmt.span().line().to_string())
                .attr("column", &stmt.span().column().to_string())
                .attr("start", &stmt.span().start().to_string())
                .attr("len", &stmt.span().len().to_string()),
        );
        self.visit_expression(*expr);
        self.emit(XmlEvent::end_element());
    }

    fn visit_function(
        &mut self,
        stmt_id: StmtId,
        ident: &Identifier,
        params: &[Parameter],
        ty: &Option<Identifier>,
        expr: &ExprId,
    ) {
        self.emit(XmlEvent::start_element("fn"));

        self.emit(
            XmlEvent::start_element("identifier")
                .attr("ref", &format!("ident:{}", ident.id()))
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(self.ast.identifier(ident.id())));
        self.emit(XmlEvent::end_element());

        if let Some(ty) = ty {
            self.emit(
                XmlEvent::start_element("type")
                    .attr("ref", &format!("ident:{}", ty.id()))
                    .attr("line", &ty.span().line().to_string())
                    .attr("column", &ty.span().column().to_string())
                    .attr("start", &ty.span().start().to_string())
                    .attr("len", &ty.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(self.ast.identifier(ty.id())));
            self.emit(XmlEvent::end_element());
        }

        self.emit(XmlEvent::start_element("parameters"));
        for (index, param) in params.iter().enumerate() {
            self.emit(
                XmlEvent::start_element("parameter")
                    .attr("id", &format!("stmt:{stmt_id}:{index}"))
                    .attr("line", &param.span().line().to_string())
                    .attr("column", &param.span().column().to_string())
                    .attr("start", &param.span().start().to_string())
                    .attr("len", &param.span().len().to_string()),
            );

            self.emit(
                XmlEvent::start_element("name")
                    .attr("ref", &format!("ident:{}", param.identifier().id()))
                    .attr("line", &param.identifier().span().line().to_string())
                    .attr("column", &param.identifier().span().column().to_string())
                    .attr("start", &param.identifier().span().start().to_string())
                    .attr("len", &param.identifier().span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                self.ast.identifier(param.identifier().id()),
            ));
            self.emit(XmlEvent::end_element());

            self.emit(
                XmlEvent::start_element("type")
                    .attr("ref", &format!("ident:{}", param.ty().id()))
                    .attr("line", &param.ty().span().line().to_string())
                    .attr("column", &param.ty().span().column().to_string())
                    .attr("start", &param.ty().span().start().to_string())
                    .attr("len", &param.ty().span().len().to_string()),
            );
            self.emit(XmlEvent::characters(self.ast.identifier(param.ty().id())));
            self.emit(XmlEvent::end_element());

            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        let expr = self.ast.expression(*expr);
        self.emit(
            XmlEvent::start_element("body")
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string()),
        );
        self.visit_expression(expr.id());
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::resolver::Resolver;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

    macro_rules! test_xml_write {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let (ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{:?}", diagnostics);

                let (ast, symbols) = Resolver::new(ast, Natives::default())
                    .resolve()
                    .expect("no error expected");

                let xml = XmlWriter::new(&ast, &symbols).serialize();
                assert_snapshot!(&xml);
            }
        };
    }

    test_xml_write!(write_unary_operator, "- 42;");
    test_xml_write!(write_expr, "40 + 2;");
    test_xml_write!(write_let, "let ident = 42;");
    test_xml_write!(write_let_fn, "let f(n: number): number = n * 2;");
    test_xml_write!(write_ret, "ret 42;");
    test_xml_write!(write_booleans, "true; false;");
    test_xml_write!(write_assignment, "let n = 0; n = 42;");
    test_xml_write!(write_if, "if true { 42; } else if false { 0; } else { 1; }");
    test_xml_write!(write_while, "while true { 42; }");
    test_xml_write!(
        write_fibonacci_rec,
        r#"
            let f(n: number): number = {
                if n <= 1 {
                    ret n;
                }
                f(n - 1) + f(n - 2);
            }
        "#
    );
    test_xml_write!(
        write_fibonacci_iter,
        r#"
            let f(n: number): number = {
                if n == 0 { ret 0; }
                if n == 1 { ret 1; }

                let prev_prev = 0;
                let prev = 1;
                let current = 0;

                let m = n;
                while m > 1 {
                    current = prev_prev + prev;
                    prev_prev = prev;
                    prev = current;
                    m = m - 1;
                }

                current;
            }
        "#
    );
}
