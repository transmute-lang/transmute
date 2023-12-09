use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{ExprId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::StatementKind;
use crate::ast::{Ast, Visitor};
use crate::symbol_table::{SymbolKind, SymbolTable};
use std::io;
use std::io::Write;
use xml::writer::XmlEvent;
use xml::{EmitterConfig, EventWriter};

#[cfg(test)]
pub fn eprint_ast(ast: Ast) -> Ast {
    let natives = crate::natives::Natives::default();
    let mut ast = ast;
    let table = crate::symbol_table::SymbolTableGen::new(&mut ast, natives).build_table();
    eprintln!("{}", XmlWriter::new(&ast, &table).serialize());
    ast
}

pub struct XmlWriter<'a> {
    ast: &'a Ast,
    table: &'a SymbolTable,
    writer: EventWriter<Vec<u8>>,
}

impl<'a> XmlWriter<'a> {
    pub fn new(ast: &'a Ast, table: &'a SymbolTable) -> Self {
        let writer = EmitterConfig::new()
            .perform_indent(true)
            .create_writer(vec![]);
        Self { ast, table, writer }
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(mut self) -> String {
        self.emit(XmlEvent::start_element("unit"));

        self.emit(XmlEvent::start_element("scopes"));
        for scope in self.table.scopes() {
            match scope.parent() {
                None => {
                    self.emit(
                        XmlEvent::start_element("scope")
                            .attr("id", &format!("scope:{}", scope.id())),
                    );
                }
                Some(parent) => self.emit(
                    XmlEvent::start_element("scope")
                        .attr("id", &format!("scope:{}", scope.id()))
                        .attr("parent", &format!("scope:{}", parent)),
                ),
            };

            for child in scope.children() {
                self.emit(
                    XmlEvent::start_element("child").attr("ref", &format!("scope:{}", child)),
                );
                self.emit(XmlEvent::end_element());
            }

            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element()); // scopes

        self.emit(XmlEvent::start_element("symbols"));
        for symbol in self.table.symbols() {
            self.emit(
                XmlEvent::start_element("symbol")
                    .attr("id", &format!("sym:{}", symbol.id()))
                    .attr("scope", &format!("scope:{}", symbol.scope())),
            );

            match symbol.kind() {
                SymbolKind::LetStatement(stmt) | SymbolKind::LetFnStatement(stmt, _) => {
                    self.emit(
                        XmlEvent::start_element("statement").attr("ref", &format!("stmt:{}", stmt)),
                    );
                    self.emit(XmlEvent::end_element());
                }
                SymbolKind::Parameter(parameter, _, _) => {
                    // todo how to link to actual parameter?
                    self.emit(
                        XmlEvent::start_element("parameter")
                            .attr(
                                "ident-ref",
                                &format!("ident:{}", parameter.identifier().id()),
                            )
                            .attr("type-ref", &format!("ident:{}", parameter.ty().id())),
                    );
                    self.emit(XmlEvent::end_element());
                }
                SymbolKind::Native(native) => {
                    self.emit(XmlEvent::start_element("native"));
                    self.emit(XmlEvent::start_element("name"));
                    self.emit(XmlEvent::characters(native.name()));
                    self.emit(XmlEvent::end_element());

                    self.emit(XmlEvent::start_element("parameters"));
                    for parameter in native.parameters() {
                        self.emit(XmlEvent::start_element("parameter"));
                        self.emit(XmlEvent::characters(&parameter.to_string()));
                        self.emit(XmlEvent::end_element());
                    }
                    self.emit(XmlEvent::end_element());

                    self.emit(XmlEvent::start_element("return"));
                    self.emit(XmlEvent::characters(&native.return_type().to_string()));
                    self.emit(XmlEvent::end_element());

                    self.emit(XmlEvent::end_element());
                }
            }

            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element()); // symbols

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
}

impl<'a> Visitor<()> for XmlWriter<'a> {
    fn visit_statement(&mut self, stmt: StmtId) {
        let stmt = self.ast.statement(stmt);
        let id = stmt.id().to_string();

        self.emit(
            XmlEvent::start_element("stmt")
                .attr("id", &format!("stmt:{id}"))
                .attr("line", &stmt.span().line().to_string())
                .attr("column", &stmt.span().column().to_string())
                .attr("start", &stmt.span().start().to_string())
                .attr("len", &stmt.span().len().to_string())
                .attr(
                    "scope",
                    &format!(
                        "scope:{}",
                        stmt.scope().map(|s| s.to_string()).unwrap_or_default()
                    ),
                ),
        );

        match stmt.kind() {
            StatementKind::Expression(expr) => {
                self.visit_expression(*expr);
            }
            StatementKind::Let(ident, expr) => {
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
            StatementKind::Ret(expr) => {
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
            StatementKind::LetFn(ident, params, ty, expr) => {
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
                for param in params {
                    self.emit(
                        XmlEvent::start_element("parameter")
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
                .attr("len", &expr.span().len().to_string())
                .attr(
                    "scope",
                    &format!(
                        "scope:{}",
                        expr.scope().map(|s| s.to_string()).unwrap_or_default()
                    ),
                ),
        );

        match expr.kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                let ident_ref = self.ast.identifier_ref(*ident_ref);

                let symbol = ident_ref
                    .symbol_id()
                    .map(|sid| self.table.symbol(sid))
                    .map(|s| match s.kind() {
                        SymbolKind::LetStatement(stmt) => {
                            format!("stmt:{stmt}")
                        }
                        SymbolKind::LetFnStatement(stmt, _) => {
                            format!("stmt:{stmt}")
                        }
                        SymbolKind::Parameter(param, _, _) => {
                            // todo add ref to parameter itself
                            format!("ident:{}", param.identifier().id())
                        }
                        SymbolKind::Native(_) => "native".to_string(),
                    })
                    .unwrap_or_default();

                self.emit(
                    XmlEvent::start_element("assign")
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        // fixme seems broken
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
            ExpressionKind::If(cond, true_branch, false_branch) => {
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
            ExpressionKind::Literal(literal) => match literal.kind() {
                LiteralKind::Boolean(b) => {
                    self.emit(XmlEvent::start_element("bool"));
                    self.emit(XmlEvent::characters(&b.to_string()));
                    self.emit(XmlEvent::end_element());
                }
                LiteralKind::Identifier(ident_ref) => {
                    let ident_ref = self.ast.identifier_ref(*ident_ref);

                    let symbol = ident_ref
                        .symbol_id()
                        .map(|sid| self.table.symbol(sid))
                        .map(|s| match s.kind() {
                            SymbolKind::LetStatement(stmt) => {
                                format!("stmt:{stmt}")
                            }
                            SymbolKind::LetFnStatement(stmt, _) => {
                                format!("stmt:{stmt}")
                            }
                            SymbolKind::Parameter(param, _, _) => {
                                // todo add ref to parameter itself
                                format!("ident:{}", param.identifier().id())
                            }
                            SymbolKind::Native(_) => "native".to_string(),
                        })
                        .unwrap_or_default();

                    self.emit(
                        XmlEvent::start_element("identifier-ref")
                            .attr("id", &format!("ident-ref:{}", ident_ref.id()))
                            .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                            // fixme seems broken
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
            },
            ExpressionKind::Binary(left, op, right) => {
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
            ExpressionKind::FunctionCall(ident_ref, params) => {
                let ident_ref = self.ast.identifier_ref(*ident_ref);

                let symbol = ident_ref
                    .symbol_id()
                    .map(|sid| self.table.symbol(sid))
                    .map(|s| match s.kind() {
                        SymbolKind::LetStatement(stmt) => {
                            format!("stmt:{stmt}")
                        }
                        SymbolKind::LetFnStatement(stmt, _) => {
                            format!("stmt:{stmt}")
                        }
                        SymbolKind::Parameter(param, _, _) => {
                            format!("ident:{}", param.identifier().id())
                        }
                        SymbolKind::Native(native) => {
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
                    .unwrap_or_default();

                self.emit(
                    XmlEvent::start_element("call")
                        .attr("line", &expr.span().line().to_string())
                        .attr("column", &expr.span().column().to_string())
                        .attr("start", &expr.span().start().to_string())
                        .attr("len", &expr.span().len().to_string())
                        // todo miss id of the ident-ref? (or remove from identifier-ref? or use identifier-ref here too)
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        .attr("name", self.ast.identifier(ident_ref.ident().id()))
                        // fixme seems broken
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
            ExpressionKind::Unary(op, expr) => {
                self.emit(
                    XmlEvent::start_element("unary").attr("operator", &op.kind().to_string()),
                );

                self.visit_expression(*expr);

                self.emit(XmlEvent::end_element());
            }
            ExpressionKind::While(cond, expr) => {
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
            ExpressionKind::Block(stmts) => {
                self.emit(XmlEvent::start_element("block"));

                #[allow(clippy::unnecessary_to_owned)]
                for stmt in stmts.to_vec() {
                    self.visit_statement(stmt);
                }

                self.emit(XmlEvent::end_element());
            }
            ExpressionKind::Dummy => {}
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_literal(&mut self, _literal: &Literal) {
        unimplemented!();
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::symbol_table::SymbolTableGen;
    use crate::type_check::TypeChecker;
    use crate::xml::XmlWriter;
    use insta::assert_snapshot;

    macro_rules! test_xml_write {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let natives = Natives::default();
                let ast_natives = Into::<crate::ast::Ast>::into(&natives);

                let (ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                assert!(diagnostics.is_empty(), "{:?}", diagnostics);

                let mut ast = ast.merge(ast_natives);
                let table = SymbolTableGen::new(&mut ast, natives).build_table();

                let (ast, diagnostics) = TypeChecker::new(ast, &table).check();

                assert!(diagnostics.is_empty(), "{:?}", diagnostics);

                let xml = XmlWriter::new(&ast, &table).serialize();
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
