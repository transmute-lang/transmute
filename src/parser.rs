use crate::ast::Ast;
use crate::error::Error;
use crate::lexer::{Lexer, Location, Span, Token, TokenKind};

pub struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Self { lexer }
    }

    pub fn parse(&mut self) -> Result<Ast, Error> {
        let token = self.lexer.next()?;

        let root = match token {
            Token {
                kind: TokenKind::Number(number),
                location,
                span,
            } => Literal::new(LiteralKind::Number(number), location, span),
        };

        Ok(Ast { root })
    }
}

#[derive(Debug, PartialEq)]
pub struct Literal {
    pub kind: LiteralKind,
    pub location: Location,
    pub span: Span,
}

impl Literal {
    fn new(kind: LiteralKind, location: Location, span: Span) -> Self {
        Self {
            kind,
            location,
            span,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum LiteralKind {
    Number(i64),
}

#[cfg(test)]
mod tests {
    use crate::ast::Ast;
    use crate::lexer::{Lexer, Location, Span};
    use crate::parser::{Literal, LiteralKind, Parser};

    #[test]
    pub fn literal() {
        let lexer = Lexer::new("42");
        let mut parser = Parser::new(lexer);

        let actual = parser.parse().unwrap();
        let expected = Ast {
            root: Literal::new(
                LiteralKind::Number(42),
                Location::new(1, 1),
                Span::new(0, 2),
            ),
        };

        assert_eq!(expected, actual);
    }
}
