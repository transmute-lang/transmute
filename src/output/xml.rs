use crate::hir::bound::Bound;
use crate::hir::expression::{Expression, ExpressionKind, Target};
use crate::hir::identifier::Identifier;
use crate::hir::literal::{Literal, LiteralKind};
use crate::hir::statement::{Field, Parameter, RetMode, Return, Statement, StatementKind};
use crate::hir::typed::Typed;
use crate::hir::ResolvedHir;
use crate::hir::{SymbolKind, Type};
use crate::ids::{ExprId, IdentRefId, StmtId};
use std::io::{self, Write};
use xml::writer::XmlEvent;
use xml::{EmitterConfig, EventWriter};

pub struct XmlWriter<'a> {
    hir: &'a ResolvedHir,
    writer: EventWriter<Vec<u8>>,
}

impl<'a> XmlWriter<'a> {
    pub fn new(ast: &'a ResolvedHir) -> Self {
        let writer = EmitterConfig::new()
            .perform_indent(true)
            .create_writer(vec![]);
        Self { hir: ast, writer }
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(mut self) -> String {
        // todo review ref, ident-ref, type-ref, target-id in ast

        self.emit(XmlEvent::start_element("unit"));

        self.emit(XmlEvent::start_element("ast"));

        self.emit(XmlEvent::start_element("identifiers"));
        for (id, identifier) in self.hir.identifiers.iter() {
            self.emit(XmlEvent::start_element("ident").attr("id", &format!("ident:{id}")));
            self.emit(XmlEvent::Characters(identifier));
            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        for stmt in self.hir.roots.iter() {
            self.visit_statement(*stmt);
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
        let stmt = &self.hir.statements[stmt];
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
            StatementKind::Ret(expr, mode) => {
                self.visit_ret(stmt, expr, mode);
            }
            StatementKind::LetFn(ident, params, ty, expr) => {
                self.visit_function(stmt.id(), ident, params, ty, expr);
            }
            StatementKind::Struct(ident, fields) => {
                self.visit_struct(stmt.id(), ident, fields);
            }
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_expression(&mut self, expr: ExprId) {
        let expr = &self.hir.expressions[expr];

        self.emit(
            XmlEvent::start_element("expr")
                .attr("id", &format!("expr:{}", expr.id()))
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string()),
        );

        match expr.kind() {
            ExpressionKind::Assignment(Target::Direct(ident_ref), rhs_expr_id) => {
                self.visit_assignment(ident_ref, rhs_expr_id);
            }
            ExpressionKind::Assignment(Target::Indirect(lhs_expr_id), rhs_expr_id) => {
                self.emit(XmlEvent::start_element("assign"));

                self.visit_expression(*lhs_expr_id);
                self.visit_expression(*rhs_expr_id);

                self.emit(XmlEvent::end_element());
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                self.visit_if(cond, true_branch, false_branch);
            }
            ExpressionKind::Literal(literal) => self.visit_literal(literal),
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                self.emit(XmlEvent::start_element("access"));
                self.visit_expression(*expr_id);

                let ident_ref = &self.hir.identifier_refs[*ident_ref_id];
                let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
                    SymbolKind::Let(stmt) => {
                        format!("stmt:{stmt}")
                    }
                    SymbolKind::LetFn(stmt, _, _) => {
                        format!("stmt:{stmt}")
                    }
                    SymbolKind::Parameter(stmt_id, index) | SymbolKind::Field(stmt_id, index) => {
                        format!("stmt:{}:{}", stmt_id, index)
                    }
                    SymbolKind::Native(..) => "native".to_string(),
                    SymbolKind::NativeType(_, _) => {
                        unreachable!("cannot assign to NativeType")
                    }
                    SymbolKind::Struct(_) => {
                        unreachable!("cannot assign to Struct")
                    }
                    SymbolKind::NotFound => panic!("symbol was not resolved"),
                };

                self.emit(
                    XmlEvent::start_element("ident")
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        .attr("target-id", &symbol),
                );

                self.emit(XmlEvent::end_element());
                self.emit(XmlEvent::end_element());
            }
            ExpressionKind::FunctionCall(ident_ref, params) => {
                self.visit_function_call(expr, ident_ref, params);
            }
            ExpressionKind::While(cond, expr) => {
                self.visit_while(cond, expr);
            }
            ExpressionKind::Block(stmts) => {
                self.visit_block(stmts);
            }
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                let ident_ref = &self.hir.identifier_refs[*ident_ref_id];

                let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
                    SymbolKind::Struct(stmt_id) => {
                        format!("stmt:{stmt_id}")
                    }
                    _ => panic!(),
                };

                self.emit(XmlEvent::start_element("struct_init"));
                self.emit(
                    XmlEvent::start_element("ident")
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        .attr("target-id", &symbol),
                );
                self.emit(XmlEvent::start_element("fields"));
                for (ident_ref_id, expr_id) in fields {
                    let ident_ref = &self.hir.identifier_refs[*ident_ref_id];
                    let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
                        SymbolKind::Field(stmt_id, index) => {
                            format!("stmt:{}:{}", stmt_id, index)
                        }
                        _ => panic!(),
                    };

                    self.emit(XmlEvent::start_element("field").attr("target-id", &symbol));
                    self.visit_expression(*expr_id);
                    self.emit(XmlEvent::end_element());
                }
                self.emit(XmlEvent::end_element());
                self.emit(XmlEvent::end_element());
            }
        }

        self.emit(XmlEvent::end_element());
    }

    fn visit_assignment(&mut self, ident_ref_id: &IdentRefId, expr: &ExprId) {
        let ident_ref = &self.hir.identifier_refs[*ident_ref_id];

        let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
            SymbolKind::Let(stmt) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::LetFn(stmt, _, _) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::Parameter(stmt_id, index) => {
                format!("stmt:{}:{}", stmt_id, index)
            }
            SymbolKind::Native(..) => "native".to_string(),
            SymbolKind::NativeType(_, _) => {
                unreachable!("cannot assign to NativeType")
            }
            SymbolKind::Field(_, _) => {
                unreachable!("cannot assign to Field")
            }
            SymbolKind::Struct(_) => {
                unreachable!("cannot assign to Struct")
            }
            SymbolKind::NotFound => panic!("symbol was not resolved"),
        };

        self.emit(
            XmlEvent::start_element("assign")
                .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                .attr("target-id", &symbol),
        );

        self.emit(XmlEvent::start_element("identifier"));
        self.emit(XmlEvent::characters(
            &self.hir.identifiers[ident_ref.ident().id()],
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

        let true_branch = &self.hir.expressions[*true_branch];
        self.emit(XmlEvent::start_element("true"));
        self.visit_expression(true_branch.id());
        self.emit(XmlEvent::end_element());

        if let Some(false_branch) = false_branch {
            let false_branch = &self.hir.expressions[*false_branch];
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
            LiteralKind::Identifier(ident_ref_id) => {
                let ident_ref = &self.hir.identifier_refs[*ident_ref_id];

                let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
                    SymbolKind::Let(stmt) => {
                        format!("stmt:{stmt}")
                    }
                    SymbolKind::LetFn(stmt, _, _) => {
                        format!("stmt:{stmt}")
                    }
                    SymbolKind::Parameter(stmt_id, index) => {
                        format!("stmt:{}:{}", stmt_id, index)
                    }
                    SymbolKind::Native(..) => "native".to_string(),
                    SymbolKind::NativeType(_, _) => {
                        unreachable!("NativeType is not a literal")
                    }
                    SymbolKind::Field(_, _) => {
                        unreachable!("Field is not a literal")
                    }
                    SymbolKind::Struct(_) => {
                        unreachable!("Struct is not a literal")
                    }
                    SymbolKind::NotFound => panic!("symbol was not resolved"),
                };

                let ty = &self.hir.types[self.hir.symbols[ident_ref.symbol_id()].type_id()];
                let type_ref = match ty {
                    Type::Struct(stmt) => match &self.hir.statements[*stmt].kind() {
                        StatementKind::Struct(_, _) => Some(format!("stmt:{stmt}")),
                        _ => unreachable!("must be a struct statement"),
                    },
                    _ => None,
                };

                self.emit(
                    XmlEvent::start_element("identifier-ref")
                        .attr("id", &format!("ident-ref:{}", ident_ref_id))
                        .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                        .attr("target-id", &symbol)
                        .attr("type-ref", &type_ref.unwrap_or_default()),
                );
                self.emit(XmlEvent::characters(
                    &self.hir.identifiers[ident_ref.ident().id()],
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

    fn visit_function_call(
        &mut self,
        expr: &Expression<Typed>,
        ident_ref_id: &IdentRefId,
        params: &[ExprId],
    ) {
        let ident_ref = &self.hir.identifier_refs[*ident_ref_id];

        let symbol = match self.hir.symbols[ident_ref.symbol_id()].kind() {
            SymbolKind::Let(stmt) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::LetFn(stmt, _, _) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::Parameter(stmt, index) => {
                let param = match &self.hir.statements[*stmt].kind() {
                    StatementKind::LetFn(_, params, _, _) => &params[*index],
                    _ => panic!(),
                };
                format!("ident:{}", param.identifier().id())
            }
            SymbolKind::Native(ident, parameters, ret_type, _) => {
                format!(
                    "native:{}:{}:{}",
                    self.hir.identifiers[*ident],
                    parameters
                        .iter()
                        .map(|p| self.hir.types[*p].to_string())
                        .collect::<Vec<String>>()
                        .join(":"),
                    self.hir.types[*ret_type]
                )
            }
            SymbolKind::NativeType(_, _) => {
                unreachable!("method call cannot be applied to NativeType")
            }
            SymbolKind::Field(_, _) => {
                unreachable!("method call cannot be applied to Field")
            }
            SymbolKind::Struct(_) => {
                unreachable!("method call cannot be applied to Struct")
            }
            SymbolKind::NotFound => {
                panic!("symbol was not resolved")
            }
        };

        self.emit(
            XmlEvent::start_element("call")
                .attr("line", &expr.span().line().to_string())
                .attr("column", &expr.span().column().to_string())
                .attr("start", &expr.span().start().to_string())
                .attr("len", &expr.span().len().to_string())
                .attr("ident-ref", &format!("ident:{}", ident_ref.ident().id()))
                .attr("name", &self.hir.identifiers[ident_ref.ident().id()])
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

    fn visit_while(&mut self, cond: &ExprId, expr: &ExprId) {
        self.emit(XmlEvent::start_element("while"));

        let cond = &self.hir.expressions[*cond];
        self.emit(
            XmlEvent::start_element("condition")
                .attr("line", &cond.span().line().to_string())
                .attr("column", &cond.span().column().to_string())
                .attr("start", &cond.span().start().to_string())
                .attr("len", &cond.span().len().to_string()),
        );
        self.visit_expression(cond.id());
        self.emit(XmlEvent::end_element());

        let expr = &self.hir.expressions[*expr];
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

    fn visit_let(&mut self, ident: &Identifier<Bound>, expr: &ExprId) {
        self.emit(XmlEvent::start_element("let"));

        self.emit(
            XmlEvent::start_element("identifier")
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(&self.hir.identifiers[ident.id()]));
        self.emit(XmlEvent::end_element());

        let expr = &self.hir.expressions[*expr];

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

    fn visit_ret(&mut self, stmt: &Statement<Typed, Bound>, expr: &ExprId, mode: &RetMode) {
        self.emit(
            XmlEvent::start_element("ret")
                .attr("mode", mode.as_str())
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
        ident: &Identifier<Bound>,
        params: &[Parameter<Typed, Bound>],
        return_type: &Return<Typed>,
        expr: &ExprId,
    ) {
        self.emit(XmlEvent::start_element("fn"));

        self.emit(
            XmlEvent::start_element("identifier")
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(&self.hir.identifiers[ident.id()]));
        self.emit(XmlEvent::end_element());

        if let Some(ty_ident_ref_id) = return_type.ident_ret_id() {
            let ty_ident_ref = &self.hir.identifier_refs[ty_ident_ref_id];

            self.emit(
                XmlEvent::start_element("type")
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                &self.hir.identifiers[ty_ident_ref.ident().id()],
            ));
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
                    .attr("line", &param.identifier().span().line().to_string())
                    .attr("column", &param.identifier().span().column().to_string())
                    .attr("start", &param.identifier().span().start().to_string())
                    .attr("len", &param.identifier().span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                &self.hir.identifiers[param.identifier().id()],
            ));
            self.emit(XmlEvent::end_element());

            let ty_ident_ref = &self.hir.identifier_refs[param.ty()];

            self.emit(
                XmlEvent::start_element("type")
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                &self.hir.identifiers[ty_ident_ref.ident().id()],
            ));
            self.emit(XmlEvent::end_element());

            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        let expr = &self.hir.expressions[*expr];
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

    fn visit_struct(
        &mut self,
        stmt_id: StmtId,
        ident: &Identifier<Bound>,
        fields: &[Field<Typed, Bound>],
    ) {
        self.emit(XmlEvent::start_element("struct"));

        self.emit(
            XmlEvent::start_element("identifier")
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(&self.hir.identifiers[ident.id()]));
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::start_element("fields"));
        for (index, param) in fields.iter().enumerate() {
            self.emit(
                XmlEvent::start_element("field")
                    .attr("id", &format!("stmt:{stmt_id}:{index}"))
                    .attr("line", &param.span().line().to_string())
                    .attr("column", &param.span().column().to_string())
                    .attr("start", &param.span().start().to_string())
                    .attr("len", &param.span().len().to_string()),
            );

            self.emit(
                XmlEvent::start_element("name")
                    .attr("line", &param.identifier().span().line().to_string())
                    .attr("column", &param.identifier().span().column().to_string())
                    .attr("start", &param.identifier().span().start().to_string())
                    .attr("len", &param.identifier().span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                &self.hir.identifiers[param.identifier().id()],
            ));
            self.emit(XmlEvent::end_element());

            let ty_ident_ref = &self.hir.identifier_refs[param.ty()];

            self.emit(
                XmlEvent::start_element("type")
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                &self.hir.identifiers[ty_ident_ref.ident().id()],
            ));
            self.emit(XmlEvent::end_element());

            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        self.emit(XmlEvent::end_element());
    }
}

#[cfg(test)]
mod tests {
    use crate::hir::UnresolvedHir;
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::output::xml::XmlWriter;
    use crate::parser::Parser;
    use insta::assert_snapshot;

    macro_rules! test_xml_write {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let hir = UnresolvedHir::from(Parser::new(Lexer::new($src)).parse().unwrap())
                    .resolve(Natives::default())
                    .unwrap();

                let xml = XmlWriter::new(&hir).serialize();
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
    test_xml_write!(write_struct, "struct S { a: number, b: number }");
    test_xml_write!(
        // todo type should be resolved and we should have a type_ref_id to point to to the ref
        //   type
        // todo also have struct as return type
        write_struct_as_type,
        "struct S { a: number, b: number } let f(s: S) = { s; }"
    );
    test_xml_write!(
        serialize_struct,
        r#"
            struct Point {
                x: number,
                y: boolean
            }

            let p = Point {
                x: 1,
                y: false
            };

            p.x;
            p.y;
        "#
    );
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
