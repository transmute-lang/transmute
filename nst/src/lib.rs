use crate::exit_points_resolver::ExitPointsResolver;
use crate::exit_points_resolver::Output as ExitPointsResolverOutput;
use crate::implicit_ret_converter::ImplicitRetResolver;
use crate::implicit_ret_converter::Output as ImplicitRetResolverOutput;
use crate::nodes::{ExitPoints, Expression, Nst, Statement, TypeDef};
use crate::operators_converter::OperatorsConverter;
use transmute_ast::statement::StatementKind as AstStatementKind;
use transmute_ast::Ast as AstAst;
use transmute_core::id_map::IdMap;
use transmute_core::ids::{ExprId, StmtId, TypeDefId};
use transmute_core::vec_map::VecMap;

pub mod builder;
mod exit_points_resolver;
mod implicit_ret_converter;
pub mod nodes;
mod operators_converter;
pub mod pretty_print;

impl From<AstAst> for Nst {
    fn from(ast: AstAst) -> Self {
        // convert operators to function calls
        let operator_free =
            OperatorsConverter::new(ast.identifiers, ast.identifier_refs).convert(ast.expressions);

        let expressions = operator_free.expressions;
        let identifiers = operator_free.identifiers;
        let identifier_refs = operator_free.identifier_refs;

        // convert implicit return statements/expressions to `Ret(..., RetMode::Implicit)`
        // statements
        let ImplicitRetResolverOutput {
            statements,
            expressions,
        } = ImplicitRetResolver::new().resolve(ast.root, ast.statements, expressions);

        // here, we have two kind of `Ret` statements:
        //  - explicit, which are present in the source code (`ret x;`)
        //  - implicit, which are not present in the source code but that happen to be the last
        //    statements on their execution path in their function

        // compute exit points, i.e. Ret statements (explicit or implicit) that are actually
        // reachable. we also compute the set of unreachable expression.
        let mut exit_points = IdMap::new();
        let mut unreachable = Vec::new();

        for (_, stmt) in statements.iter() {
            if let &AstStatementKind::LetFn(_, _, _, _, expr_id) = &stmt.kind {
                let ExitPointsResolverOutput {
                    exit_points: new_exit_points,
                    unreachable: mut new_unreachable,
                } = ExitPointsResolver::new(&expressions, &statements).resolve(expr_id);

                #[cfg(test)]
                println!("{}:{}: Computed exit points={new_exit_points:?} and unreachable={new_unreachable:?} for {expr_id:?}", file!(), line!());

                exit_points.insert(expr_id, new_exit_points);
                unreachable.append(&mut new_unreachable);
            }
        }

        unreachable.sort();
        unreachable.dedup();

        Self {
            identifiers,
            identifier_refs,
            expressions: expressions
                .into_iter()
                .map(|e| (e.0, Expression::from(e.1)))
                .collect::<VecMap<ExprId, Expression>>(),
            statements: statements
                .into_iter()
                .map(|s| (s.0, Statement::from(s.1)))
                .collect::<VecMap<StmtId, Statement>>(),
            type_defs: ast
                .type_defs
                .into_iter()
                .map(|e| (e.0, TypeDef::from(e.1)))
                .collect::<VecMap<TypeDefId, TypeDef>>(),
            root: ast.root,
            exit_points: ExitPoints {
                exit_points,
                unreachable,
            },
        }
    }
}
