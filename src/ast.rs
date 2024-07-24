pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod literal;
pub mod operators;
pub mod statement;

use crate::ast::expression::Expression;
use crate::ast::identifier_ref::IdentifierRef;
use crate::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::statement::Statement;
use crate::vec_map::VecMap;

// todo now fields are public, cleanup getters
#[derive(Debug, PartialEq)]
pub struct Ast {
    /// Unique identifiers names
    pub identifiers: VecMap<IdentId, String>,
    /// Identifier refs
    pub identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    /// All expressions
    pub expressions: VecMap<ExprId, Expression>,
    /// All statements
    pub statements: VecMap<StmtId, Statement>,
    /// Root statements
    pub root: Vec<StmtId>,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: Vec<IdentifierRef>,
        expressions: Vec<Expression>,
        statements: Vec<Statement>,
        root: Vec<StmtId>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs: identifier_refs.into(),
            expressions: expressions.into(),
            statements: statements.into(),
            root,
        }
    }

    pub fn identifiers(&self) -> &VecMap<IdentId, String> {
        &self.identifiers
    }

    pub fn identifier(&self, id: IdentId) -> &str {
        &self.identifiers[id]
    }

    pub fn identifier_ref(&self, id: IdentRefId) -> &IdentifierRef {
        &self.identifier_refs[id]
    }

    pub fn expression(&self, id: ExprId) -> &Expression {
        &self.expressions[id]
    }

    pub fn statement(&self, id: StmtId) -> &Statement {
        &self.statements[id]
    }

    pub fn roots(&self) -> &Vec<StmtId> {
        &self.root
    }

    #[cfg(test)]
    pub fn identifier_ref_id(&self, start: usize) -> IdentRefId {
        for (id, ident_ref) in &self.identifier_refs {
            if ident_ref.ident().span().start() == start {
                return id;
            }
        }
        panic!("No identifier ref found at {}", start)
    }

    #[cfg(test)]
    pub fn expressions(&self) -> &VecMap<ExprId, Expression> {
        &self.expressions
    }

    #[cfg(test)]
    pub fn statements(&self) -> &VecMap<StmtId, Statement> {
        &self.statements
    }

    #[cfg(test)]
    pub fn expression_id(&self, start: usize) -> ExprId {
        for (id, expr) in &self.expressions {
            if expr.span().start() == start {
                return id;
            }
        }
        panic!("No expression found at {}", start)
    }

    #[cfg(test)]
    pub fn statement_id(&self, start: usize) -> StmtId {
        for (id, stmt) in &self.statements {
            if stmt.span().start() == start {
                return id;
            }
        }
        panic!("No statement found at {}", start)
    }
}
