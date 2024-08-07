use bimap::BiMap;
use transmute_ast::expression::{Expression, ExpressionKind};
use transmute_ast::identifier::Identifier;
use transmute_ast::identifier_ref::IdentifierRef;
use transmute_core::ids::{ExprId, IdentId, IdentRefId};
use transmute_core::vec_map::VecMap;

pub struct OperatorsConverter {
    identifiers: BiMap<IdentId, String>,
    identifier_refs: VecMap<IdentRefId, IdentifierRef>,
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
        }
    }

    pub fn convert(mut self, expressions: VecMap<ExprId, Expression>) -> Output {
        let expressions = expressions
            .into_iter()
            .map(|(expr_ir, expr)| (expr_ir, self.convert_expression(expr)))
            .collect::<VecMap<ExprId, Expression>>();

        let identifiers = self
            .identifiers
            .into_iter()
            .collect::<VecMap<IdentId, String>>();

        Output {
            identifiers,
            identifier_refs: self.identifier_refs,
            expressions,
        }
    }

    fn convert_expression(&mut self, expression: Expression) -> Expression {
        match expression.kind() {
            ExpressionKind::Binary(lhs_id, op, rhs_id) => {
                let ident_id = self.ident_id(op.kind().function_name());
                let identifier = Identifier::new(ident_id, op.span().clone());
                let ident_ref_id = IdentRefId::from(self.identifier_refs.len());
                self.identifier_refs
                    .push(IdentifierRef::new(ident_ref_id, identifier));

                Expression::new(
                    expression.id(),
                    ExpressionKind::FunctionCall(ident_ref_id, vec![*lhs_id, *rhs_id]),
                    expression.span().clone(),
                )
            }
            ExpressionKind::Unary(op, expr_id) => {
                let ident_id = self.ident_id(op.kind().function_name());
                let identifier = Identifier::new(ident_id, op.span().clone());
                let ident_ref_id = IdentRefId::from(self.identifier_refs.len());
                self.identifier_refs
                    .push(IdentifierRef::new(ident_ref_id, identifier));

                Expression::new(
                    expression.id(),
                    ExpressionKind::FunctionCall(ident_ref_id, vec![*expr_id]),
                    expression.span().clone(),
                )
            }
            _ => expression,
        }
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

    macro_rules! op {
        ($name: ident, $src:expr) => {
            #[test]
            fn $name() {
                let ast = Parser::new(Lexer::new($src)).parse().unwrap();
                let output = OperatorsConverter::new(ast.identifiers, ast.identifier_refs)
                    .convert(ast.expressions);

                let ast = Ast {
                    identifiers: output.identifiers,
                    identifier_refs: output.identifier_refs,
                    expressions: output.expressions,
                    statements: ast.statements,
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
