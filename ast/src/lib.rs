use crate::expression::Expression;
use crate::identifier_ref::IdentifierRef;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::statement::Statement;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId};
use transmute_core::vec_map::VecMap;

pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod lexer;
pub mod literal;
pub mod operators;
pub mod parser;
pub mod pretty_print;
pub mod statement;

pub fn parse(input: &str) -> Result<Ast, Diagnostics> {
    Parser::new(Lexer::new(input)).parse()
}

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
    pub roots: Vec<StmtId>,
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
            roots: root,
        }
    }
}
