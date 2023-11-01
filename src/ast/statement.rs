use crate::ast::expression::Expression;
use crate::ast::identifier::Identifier;
use crate::lexer::Span;

#[derive(Debug, PartialEq)]
pub struct Statement<'s> {
    // todo should be merged with Expression, maybe?
    kind: StatementKind<'s>,
    span: Span,
}

impl<'s> Statement<'s> {
    pub fn new(kind: StatementKind<'s>, span: Span) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &StatementKind<'s> {
        &self.kind
    }
}

#[derive(Debug, PartialEq)]
pub enum StatementKind<'s> {
    Expression(Expression<'s>),
    Let(Identifier<'s>, Expression<'s>),
    Ret(Expression<'s>),
    // todo vec does not hold span and position as it should (search for "Vec<Statement>, Span")
    LetFn(Identifier<'s>, Vec<Identifier<'s>>, Vec<Statement<'s>>),
}
