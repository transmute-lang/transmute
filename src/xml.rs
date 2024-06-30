use crate::ast::expression::{Expression, ExpressionKind, Target, Typed};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::Bound;
use crate::ast::ids::{ExprId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{BinaryOperator, UnaryOperator};
use crate::ast::statement::{Field, Parameter, RetMode, Return, Statement, StatementKind};
use crate::ast::ResolvedAst;
use crate::resolver::{SymbolKind, Type};
use std::io::{self, Write};
use xml::writer::XmlEvent;
use xml::{EmitterConfig, EventWriter};

pub struct XmlWriter<'a> {
    ast: &'a ResolvedAst,
    writer: EventWriter<Vec<u8>>,
}

impl<'a> XmlWriter<'a> {
    pub fn new(ast: &'a ResolvedAst) -> Self {
        let writer = EmitterConfig::new()
            .perform_indent(true)
            .create_writer(vec![]);
        Self { ast, writer }
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(mut self) -> String {
        // todo review ref, ident-ref, type-ref, target-id in ast

        self.emit(XmlEvent::start_element("unit"));

        self.emit(XmlEvent::start_element("ast"));

        self.emit(XmlEvent::start_element("identifiers"));
        for (id, identifier) in self.ast.identifiers().iter() {
            self.emit(XmlEvent::start_element("ident").attr("id", &format!("ident:{id}")));
            self.emit(XmlEvent::Characters(identifier));
            self.emit(XmlEvent::end_element());
        }
        self.emit(XmlEvent::end_element());

        #[allow(clippy::unnecessary_to_owned)]
        for stmt in self.ast.root_statements().to_vec() {
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
            ExpressionKind::Binary(left, op, right) => {
                self.visit_binary_operator(expr, left, op, right);
            }
            ExpressionKind::Access(expr_id, ident_ref_id) => {
                self.emit(XmlEvent::start_element("access"));
                self.visit_expression(*expr_id);

                let ident_ref = self.ast.identifier_ref(*ident_ref_id);
                let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
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
                    SymbolKind::NotFound => panic!(),
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
            ExpressionKind::StructInstantiation(ident_ref_id, fields) => {
                let ident_ref = self.ast.identifier_ref(*ident_ref_id);

                let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
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
                    let ident_ref = self.ast.identifier_ref(*ident_ref_id);
                    let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
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
        let ident_ref = self.ast.identifier_ref(*ident_ref_id);

        let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
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
            SymbolKind::NotFound => panic!(),
        };

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
            LiteralKind::Identifier(ident_ref_id) => {
                let ident_ref = self.ast.identifier_ref(*ident_ref_id);

                let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
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
                    SymbolKind::NotFound => panic!(),
                };

                let ty = self.ast.ty(self.ast.symbol(ident_ref.symbol_id()).ty());
                let type_ref = match ty {
                    Type::Struct(stmt) => match self.ast.statement(*stmt).kind() {
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
        expr: &Expression<Typed>,
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
        expr: &Expression<Typed>,
        ident_ref_id: &IdentRefId,
        params: &[ExprId],
    ) {
        let ident_ref = self.ast.identifier_ref(*ident_ref_id);

        let symbol = match self.ast.symbol(ident_ref.symbol_id()).kind() {
            SymbolKind::Let(stmt) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::LetFn(stmt, _, _) => {
                format!("stmt:{stmt}")
            }
            SymbolKind::Parameter(stmt, index) => {
                let param = match self.ast.statement(*stmt).kind() {
                    StatementKind::LetFn(_, params, _, _) => &params[*index],
                    _ => panic!(),
                };
                format!("ident:{}", param.identifier().id())
            }
            SymbolKind::Native(ident, parameters, ret_type, _) => {
                format!(
                    "native:{}:{}:{}",
                    self.ast.identifier(*ident),
                    parameters
                        .iter()
                        .map(|p| self.ast.ty(*p).to_string())
                        .collect::<Vec<String>>()
                        .join(":"),
                    self.ast.ty(*ret_type)
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
                // todo we dont want to get there... an unresolved symbol must not lead to a
                //   resolved AST
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

    fn visit_let(&mut self, ident: &Identifier<Bound>, expr: &ExprId) {
        self.emit(XmlEvent::start_element("let"));

        self.emit(
            XmlEvent::start_element("identifier")
                // todo not sure this is really useful, we have the full name in the tag anyway
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
        return_type: &Return,
        expr: &ExprId,
    ) {
        self.emit(XmlEvent::start_element("fn"));

        self.emit(
            XmlEvent::start_element("identifier")
                // todo not sure this is really useful, we have the full name in the tag anyway
                .attr("ref", &format!("ident:{}", ident.id()))
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(self.ast.identifier(ident.id())));
        self.emit(XmlEvent::end_element());

        if let Some(ty_ident_ref_id) = return_type.ident_ret_id() {
            let ty_ident_ref = self.ast.identifier_ref(ty_ident_ref_id);

            self.emit(
                XmlEvent::start_element("type")
                    // todo add ref to actual type
                    .attr("ref", &format!("ident:{}", ty_ident_ref.ident().id()))
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                self.ast.identifier(ty_ident_ref.ident().id()),
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

            let ty_ident_ref = self.ast.identifier_ref(param.ty());

            self.emit(
                XmlEvent::start_element("type")
                    // todo add ref to actual type
                    .attr("ref", &format!("ident:{}", ty_ident_ref.ident().id()))
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                self.ast.identifier(ty_ident_ref.ident().id()),
            ));
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

    fn visit_struct(
        &mut self,
        stmt_id: StmtId,
        ident: &Identifier<Bound>,
        fields: &[Field<Typed, Bound>],
    ) {
        self.emit(XmlEvent::start_element("struct"));

        self.emit(
            XmlEvent::start_element("identifier")
                // todo not sure this is really useful, we have the full name in the tag anyway
                .attr("ref", &format!("ident:{}", ident.id()))
                .attr("line", &ident.span().line().to_string())
                .attr("column", &ident.span().column().to_string())
                .attr("start", &ident.span().start().to_string())
                .attr("len", &ident.span().len().to_string()),
        );
        self.emit(XmlEvent::characters(self.ast.identifier(ident.id())));
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

            let ty_ident_ref = self.ast.identifier_ref(param.ty());

            self.emit(
                XmlEvent::start_element("type")
                    // todo add ref to actual type
                    .attr("ref", &format!("ident:{}", ty_ident_ref.ident().id()))
                    .attr("line", &ty_ident_ref.span().line().to_string())
                    .attr("column", &ty_ident_ref.span().column().to_string())
                    .attr("start", &ty_ident_ref.span().start().to_string())
                    .attr("len", &ty_ident_ref.span().len().to_string()),
            );
            self.emit(XmlEvent::characters(
                self.ast.identifier(ty_ident_ref.ident().id()),
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
    use crate::desugar::ImplicitRetConverter;
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
                let ast = Parser::new(Lexer::new($src))
                    .parse()
                    .unwrap()
                    .convert_implicit_ret(ImplicitRetConverter::new())
                    .resolve(Resolver::new(), Natives::default())
                    .unwrap();

                let xml = XmlWriter::new(&ast).serialize();
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
