use crate::expression::Expression;
use crate::identifier_ref::IdentifierRef;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::statement::{Statement, TypeDef};
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, StmtId, TypeDefId};
use transmute_core::vec_map::VecMap;

pub mod annotation;
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
    /// Types
    pub type_defs: VecMap<TypeDefId, TypeDef>,
    /// Root statements
    pub roots: Vec<StmtId>,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: VecMap<IdentRefId, IdentifierRef>,
        expressions: Vec<Expression>,
        statements: VecMap<StmtId, Statement>,
        roots: Vec<StmtId>,
        type_defs: VecMap<TypeDefId, TypeDef>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs,
            expressions: expressions.into(),
            statements,
            type_defs,
            roots,
        }
    }
}
