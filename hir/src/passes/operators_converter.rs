use bimap::BiMap;
use transmute_ast::expression::{Expression, ExpressionKind};
use transmute_ast::identifier::Identifier;
use transmute_ast::identifier_ref::IdentifierRef;
use transmute_ast::literal::{Literal, LiteralKind};
use transmute_core::ids::{ExprId, IdentId, IdentRefId};
use transmute_core::span::Span;
use transmute_core::vec_map::VecMap;

pub struct OperatorsConverter {
    identifiers: BiMap<IdentId, String>,
    identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    expressions: VecMap<ExprId, Expression>,
}

pub struct Output {
    pub identifiers: VecMap<IdentId, String>,
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    pub expressions: VecMap<ExprId, Expression>,
}

impl OperatorsConverter {
    pub fn new(
        identifiers: VecMap<IdentId, String>,
        identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    ) -> Self {
        Self {
            identifiers: identifiers.into_iter().collect::<BiMap<IdentId, String>>(),
            identifier_refs,
            expressions: VecMap::new(),
        }
    }

    pub fn convert(mut self, expressions: VecMap<ExprId, Expression>) -> Output {
        self.expressions.resize(expressions.len());

        for (_, expression) in expressions {
            self.convert_expression(expression);
        }

        let identifiers = self
            .identifiers
            .into_iter()
            .collect::<VecMap<IdentId, String>>();

        Output {
            identifiers,
            identifier_refs: self.identifier_refs,
            expressions: self.expressions,
        }
    }

    fn convert_expression(&mut self, expression: Expression) {
        let (expr_id, expression) = match &expression.kind {
            ExpressionKind::Binary(lhs_id, op, rhs_id) => {
                let ident_expr_id =
                    self.gen_fn_ident_ref_expression(&op.span, op.kind.function_name());

                (
                    expression.id,
                    Expression::new(
                        expression.id,
                        ExpressionKind::FunctionCall(ident_expr_id, vec![*lhs_id, *rhs_id]),
                        expression.span.clone(),
                    ),
                )
            }
            ExpressionKind::Unary(op, expr_id) => {
                let ident_expr_id =
                    self.gen_fn_ident_ref_expression(&op.span, op.kind.function_name());

                (
                    expression.id,
                    Expression::new(
                        expression.id,
                        ExpressionKind::FunctionCall(ident_expr_id, vec![*expr_id]),
                        expression.span.clone(),
                    ),
                )
            }
            _ => (expression.id, expression),
        };

        self.expressions.insert(expr_id, expression);
    }

    fn gen_fn_ident_ref_expression(&mut self, span: &Span, function_name: &'static str) -> ExprId {
        let ident_id = self.ident_id(function_name);
        let identifier = Identifier::new(ident_id, span.clone());
        let ident_ref_id = self.identifier_refs.create();
        self.identifier_refs
            .insert(ident_ref_id, IdentifierRef::new(ident_ref_id, identifier));

        let ident_expr_id = self.expressions.next_index();
        self.expressions.insert(
            ident_expr_id,
            Expression {
                id: ident_expr_id,
                kind: ExpressionKind::Literal(Literal {
                    kind: LiteralKind::Identifier(ident_ref_id),
                    span: span.clone(),
                }),
                span: span.clone(),
            },
        );
        ident_expr_id
    }

    fn ident_id(&mut self, function_name: &'static str) -> IdentId {
        if !self.identifiers.contains_right(function_name) {
            let ident_id = IdentId::from(self.identifiers.len());
            self.identifiers.insert(ident_id, function_name.to_string());
        }

        *self
            .identifiers
            .get_by_right(function_name)
            .expect("it is there")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_ast::pretty_print::Options;
    use transmute_ast::Ast;
    use transmute_ast::CompilationUnit;
    use transmute_core::ids::InputId;

    macro_rules! op {
        ($name: ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit = CompilationUnit::default();
                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), $src),
                )
                .parse();
                let ast = compilation_unit.into_ast().unwrap();
                let output = OperatorsConverter::new(ast.identifiers, ast.identifier_refs)
                    .convert(ast.expressions);

                let ast = Ast {
                    identifiers: output.identifiers,
                    identifier_refs: output.identifier_refs,
                    expressions: output.expressions,
                    statements: ast.statements,
                    type_defs: ast.type_defs,
                    roots: ast.roots,
                };

                let mut w = String::new();
                ast.pretty_print(&Options::default(), &mut w).unwrap();

                assert_snapshot!(w);
            }
        };
    }

    op!(add, "lhs + rhs;");
    op!(sub, "lhs - rhs;");
    op!(mul, "lhs * rhs;");
    op!(div, "lhs / rhs;");
    op!(eq, "lhs == rhs;");
    op!(neq, "lhs != rhs;");
    op!(gt, "lhs > rhs;");
    op!(ge, "lhs >= rhs;");
    op!(lt, "lhs < rhs;");
    op!(le, "lhs <= rhs;");

    op!(minus, "- op;");
}
