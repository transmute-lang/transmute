use crate::ast;
use crate::ast::expression::{ExpressionKind, Untyped};
use crate::ast::identifier::Identifier;
use crate::ast::identifier_ref::{IdentifierRef, Unbound};
use crate::ast::ids::{ExprId, IdentId, IdentRefId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::operators::{
    BinaryOperator, BinaryOperatorKind, Precedence, UnaryOperator, UnaryOperatorKind,
};
use crate::ast::statement::{Field, Parameter, RetMode, Return, StatementKind};
use crate::ast::{Ast, ImplicitRet};
use crate::error::Diagnostics;
use crate::lexer::{Lexer, PeekableLexer, Span, Token, TokenKind};
use std::collections::{HashMap, HashSet};

type Expression = ast::expression::Expression<Untyped>;
type Statement = ast::statement::Statement<Untyped, Unbound>;

pub struct Parser<'s> {
    lexer: PeekableLexer<'s>,
    identifiers: HashMap<String, IdentId>,
    identifier_refs: Vec<IdentifierRef<Unbound>>,
    expressions: Vec<Expression>,
    statements: Vec<Statement>,
    diagnostics: Diagnostics,
    expected: HashSet<TokenKind>,
    eof: bool,
}

/// Reports an unexpected token, together with the token that were expected. Does not update
/// the token stream.
macro_rules! report_unexpected_token {
    ($self:ident, $token:ident, [$($expected:expr,)*]) => {
        if !$self.eof {
            for e in vec![$($expected),*] {
                $self.expected.insert(e);
            }
            let mut expected = $self
                .expected
                .iter()
                .collect::<Vec<_>>();
            expected.sort();
            $self.diagnostics.report_err(
                format!(
                    "Unexpected {}, expected one of {}",
                    $token.kind(),
                    expected
                        .into_iter()
                        .map(|e| e.to_string())
                        .collect::<Vec<String>>()
                        .join(", ")
                ),
                $token.span().clone(),
                (file!(), line!()),
            );
        }
        $self.expected.clear();
        if $token.kind() == &TokenKind::Eof {
            $self.eof = true;
        }
    };
}

/// Reports a missing token, together with the token that was found instead. Does not alter the
/// token stream but evaluates to the expected token
// todo as we never use the returned token, assess whether this macro is still used (could be
//   replaced with `report_unexpected_token` instead?
// todo or, use only use when the next token is the one that comes after the missing expected one
macro_rules! report_and_insert_missing_token {
    ($self:ident, $token:ident, $expected:expr) => {{
        if !$self.eof {
            $self.diagnostics.report_err(
                format!("Expected {}, got {}", $expected, $token.kind()),
                $token.span().clone(),
                (file!(), line!()),
            );
        }
        if $token.kind() == &TokenKind::Eof {
            $self.eof = true;
        }
        $self.expected.clear();
        crate::lexer::Token::new(
            $expected,
            Span::new(
                $token.span().line(),
                $token.span().column(),
                $token.span().start(),
                0,
            ),
        )
    }};
}

/// Reports a missing closing token, together with the information about what is the corresponding
/// opening token and the token that was found instead. Evaluates to the missing token.
macro_rules! report_and_insert_missing_closing_token {
    ($self:ident, $token:ident, $expected:expr, $open_token:expr, $open_span:expr) => {{
        if !$self.eof {
            $self.diagnostics.report_err(
                format!(
                    "Expected {} to close {} at {}:{}, got {}",
                    $expected,
                    $open_token,
                    $open_span.line(),
                    $open_span.column(),
                    $token.kind()
                ),
                $token.span().clone(),
                (file!(), line!()),
            );
        }
        if $token.kind() == &TokenKind::Eof {
            $self.eof = true;
        }
        $self.expected.clear();
        crate::lexer::Token::new(
            $expected,
            Span::new(
                $token.span().line(),
                $token.span().column(),
                $token.span().start(),
                0,
            ),
        )
    }};
}

impl<'s> Parser<'s> {
    pub fn new(lexer: Lexer<'s>) -> Self {
        Self {
            lexer: PeekableLexer::new(lexer, 1),
            identifiers: Default::default(),
            identifier_refs: Default::default(),
            expressions: Default::default(),
            statements: Default::default(),
            diagnostics: Default::default(),
            expected: HashSet::default(),
            eof: false,
        }
    }

    pub fn parse(mut self) -> Result<Ast<ImplicitRet, Untyped, Unbound>, Diagnostics> {
        let mut statements = Vec::new();

        while let Some(statement) = self.parse_statement() {
            statements.push(statement.id());
        }

        let mut identifiers = self
            .identifiers
            .into_iter()
            .collect::<Vec<(String, IdentId)>>();

        identifiers.sort_by(|(_, id1), (_, id2)| id1.id().cmp(&id2.id()));

        let identifiers = identifiers
            .into_iter()
            .map(|(ident, _)| ident)
            .collect::<Vec<String>>();

        if self.diagnostics.is_empty() {
            Ok(Ast::new(
                identifiers,
                self.identifier_refs,
                self.expressions,
                self.statements,
                statements,
            ))
        } else {
            Err(self.diagnostics)
        }
    }

    /// Parses the following:
    /// ```
    /// 'let ident = expr ;
    /// 'let ident ( expr , ... ) = expr ;
    /// 'let ident ( expr , ... ) = { expr ; ... }
    /// `struct ident { ident : ident , ... }`
    /// 'expr ;
    /// 'ret expr ;
    /// ```
    fn parse_statement(&mut self) -> Option<&Statement> {
        let token = self.lexer.peek();

        if token.kind() == &TokenKind::Eof {
            return None;
        }
        // todo allow empty statement

        match token.kind() {
            TokenKind::Let => {
                // self.expected.clear();
                let let_token = self.lexer.next();
                let identifier_token = self.lexer.next();
                let identifier = match identifier_token.kind() {
                    TokenKind::Identifier => Identifier::new(
                        self.push_identifier(identifier_token.span()),
                        identifier_token.span().clone(),
                    ),
                    _ => {
                        report_unexpected_token!(self, identifier_token, [TokenKind::Identifier,]);
                        self.take_until_one_of(vec![TokenKind::Semicolon]);
                        return None;
                    }
                };

                let token = self.lexer.peek();

                if token.kind() == &TokenKind::OpenParenthesis {
                    // self.expected.clear();
                    // let ident '( expr , ... ) = expr ;
                    return self.parse_function(let_token.span(), identifier);
                }

                // let ident = 'expr ;

                let token = self.lexer.next();
                if token.kind() != &TokenKind::Equal {
                    report_and_insert_missing_token!(self, token, TokenKind::Equal);
                    self.lexer.push_next(token);
                }

                let expression = self.parse_expression().id();
                let semicolon = self.parse_semicolon();
                let span = let_token.span().extend_to(semicolon.span());

                let id = self.push_statement(StatementKind::Let(identifier, expression), span);
                Some(&self.statements[id.id()])
            }
            TokenKind::Ret => {
                // self.expected.clear();
                let ret_token = self.lexer.next();
                let expression = self.parse_expression().id();
                let semicolon = self.parse_semicolon();
                let span = ret_token.span().extend_to(semicolon.span());

                let id =
                    self.push_statement(StatementKind::Ret(expression, RetMode::Explicit), span);
                Some(&self.statements[id.id()])
            }
            TokenKind::If | TokenKind::While => {
                // todo could call `parse_if_expression` without going through `parse_expression`
                // self.expected.clear();
                let expression = self.parse_expression();
                let span = expression.span().extend_to(expression.span());
                let id = expression.id();
                let id = self.push_statement(StatementKind::Expression(id), span);
                Some(&self.statements[id.id()])
            }
            TokenKind::False
            | TokenKind::Identifier
            | TokenKind::Minus
            | TokenKind::Number(_)
            | TokenKind::OpenParenthesis
            | TokenKind::True => {
                // self.expected.clear();
                let expression = self.parse_expression();
                let span = expression.span().clone();
                let expression = expression.id();

                let semicolon = self.parse_semicolon();
                let span = span.extend_to(semicolon.span());

                let id = self.push_statement(StatementKind::Expression(expression), span);
                Some(&self.statements[id.id()])
            }
            TokenKind::Struct => self.parse_struct(),
            _ => {
                report_unexpected_token!(
                    self,
                    token,
                    [
                        TokenKind::Identifier,
                        TokenKind::Number(0),
                        TokenKind::Minus,
                        TokenKind::True,
                        TokenKind::False,
                        TokenKind::OpenParenthesis,
                        TokenKind::Let,
                        TokenKind::Ret,
                        TokenKind::If,
                        TokenKind::While,
                    ]
                );
                match self.lexer.next().kind() {
                    TokenKind::Eof => None,
                    _ => {
                        // try again after having consumed the unexpected token
                        self.parse_statement()
                    }
                }
            }
        }
    }

    /// Parses the following:
    /// ```
    /// let ident '( param , ... ): type = expr ;
    /// let ident '( param , ... ): type = { expr ; ... } ;
    /// ```
    fn parse_function(&mut self, span: &Span, identifier: Identifier) -> Option<&Statement> {
        // let name '( param , ... ): type = expr ;
        let open_parenthesis_token = self.lexer.next();
        assert_eq!(open_parenthesis_token.kind(), &TokenKind::OpenParenthesis);

        let mut parameters = Vec::new();
        let mut next = TokenKind::Identifier;

        loop {
            // todo review parameters parsing (see struct)
            let token = self.lexer.next();
            match token.kind() {
                TokenKind::CloseParenthesis => {
                    // self.expected.clear();
                    break;
                }
                TokenKind::Comma if next == TokenKind::Comma => {
                    // self.expected.clear();
                    next = TokenKind::Identifier;
                }
                TokenKind::Identifier if next == TokenKind::Identifier => {
                    // self.expected.clear();
                    let ident =
                        Identifier::new(self.push_identifier(token.span()), token.span().clone());

                    let colon = self.lexer.next();
                    let mut error = false;
                    if colon.kind() != &TokenKind::Colon {
                        report_and_insert_missing_token!(self, colon, TokenKind::Colon);
                        error = true;
                        self.lexer.push_next(colon);
                    }

                    let ty = self.lexer.next();
                    if ty.kind() != &TokenKind::Identifier {
                        if !error {
                            report_unexpected_token!(self, ty, [TokenKind::Identifier,]);
                        }
                        self.lexer.push_next(ty);
                        next = TokenKind::Comma;
                        continue;
                    }
                    let ty = Identifier::new(self.push_identifier(ty.span()), ty.span().clone());

                    let span = ident.span().extend_to(ty.span());
                    parameters.push(Parameter::new(ident, ty, span));
                    next = TokenKind::Comma;
                }
                TokenKind::Eof => {
                    report_unexpected_token!(
                        self,
                        token,
                        [next.clone(), TokenKind::CloseParenthesis,]
                    );
                    return None;
                }
                _ => {
                    report_unexpected_token!(
                        self,
                        token,
                        [next.clone(), TokenKind::CloseParenthesis,]
                    );
                    self.take_until_one_of(vec![
                        TokenKind::Identifier,
                        TokenKind::CloseParenthesis,
                    ]);
                }
            }
        }

        let colon = self.lexer.next();
        let ty = if colon.kind() == &TokenKind::Colon {
            let ty = self.lexer.next();
            if ty.kind() == &TokenKind::Identifier {
                Return::some(
                    Identifier::new(self.push_identifier(ty.span()), ty.span().clone()),
                    Unbound,
                )
            } else {
                self.lexer.push_next(ty);
                Return::none()
            }
        } else {
            self.lexer.push_next(colon);
            Return::none()
        };

        // let name ( param , ... ): type '= expr ;
        let token = self.lexer.next();
        if token.kind() != &TokenKind::Equal {
            // todo allow to skip the equal sign if the next token is {
            report_and_insert_missing_token!(self, token, TokenKind::Equal);
            self.lexer.push_next(token);
        }

        let (expr_id, end_span) = if self.lexer.peek().kind() == &TokenKind::OpenCurlyBracket {
            // let name ( param , ... ): type = '{ expr ; ... }
            let open_curly_bracket = self.lexer.next();

            let (statements, statements_span) = self.parse_statements(open_curly_bracket.span());

            (
                self.push_expression(
                    ExpressionKind::Block(statements),
                    open_curly_bracket.span().extend_to(&statements_span),
                ),
                statements_span,
            )
        } else {
            // let name ( param , ... ): type = 'expr ;
            let expression = self.parse_expression();
            let expr_id = expression.id();
            let expr_span = expression.span().clone();

            let semicolon_token = self.parse_semicolon();
            let end_span = expr_span.extend_to(semicolon_token.span());

            let stmt_id = self.push_statement(StatementKind::Expression(expr_id), end_span.clone());

            (
                self.push_expression(ExpressionKind::Block(vec![stmt_id]), end_span.clone()),
                end_span,
            )
        };

        let id = self.push_statement(
            StatementKind::LetFn(identifier, parameters, ty, expr_id),
            span.extend_to(&end_span),
        );

        Some(&self.statements[id.id()])
    }

    fn parse_struct(&mut self) -> Option<&Statement> {
        // 'struct ident { ident : ident , ... }
        let token_struct = self.lexer.next();
        let identifier_token = self.lexer.next();
        let identifier = match identifier_token.kind() {
            TokenKind::Identifier => Identifier::new(
                self.push_identifier(identifier_token.span()),
                identifier_token.span().clone(),
            ),
            _ => {
                report_unexpected_token!(self, identifier_token, [TokenKind::Identifier,]);
                self.take_until_one_of(vec![TokenKind::CloseCurlyBracket, TokenKind::Semicolon]);
                return None;
            }
        };

        // struct ident '{ ident : ident , ... }
        let token = self.lexer.next();
        if token.kind() != &TokenKind::OpenCurlyBracket {
            report_and_insert_missing_token!(self, token, TokenKind::OpenCurlyBracket);
            self.lexer.push_next(token);
        }

        let mut fields = Vec::new();
        let mut expect_more = true;

        let last_token = loop {
            // struct ident { ... , 'ident : ident , ... }
            let token = self.lexer.next();
            match token.kind() {
                TokenKind::CloseCurlyBracket => {
                    // struct ident { ... '}
                    break token;
                }
                TokenKind::Identifier => {
                    // struct ident { ... , 'ident : ident , ... }
                    if !expect_more {
                        // we did not finish the previous field with a comma but got the
                        // identifier of a new one. report the error and continue as if the comma
                        // was there
                        report_unexpected_token!(
                            self,
                            token,
                            [TokenKind::Colon, TokenKind::CloseCurlyBracket,]
                        );
                    }

                    let ident =
                        Identifier::new(self.push_identifier(token.span()), token.span().clone());
                    expect_more = false;

                    // struct ident { ... , ident ': ident , ... }

                    let token = self.lexer.next();
                    match token.kind() {
                        TokenKind::Colon => {}
                        _ => {
                            // we missed the colon
                            report_unexpected_token!(self, token, [TokenKind::Colon,]);
                            self.take_until_one_of(vec![
                                TokenKind::Colon,
                                TokenKind::Identifier,
                                TokenKind::Comma,
                                TokenKind::CloseCurlyBracket,
                            ]);

                            let token = self.lexer.next();
                            match token.kind() {
                                TokenKind::Colon => {
                                    // we finally found a colon, we continue parsing the current
                                    // field from here, ignoring everything between the field name
                                    // and the colon we just found

                                    // struct ident { ... , ident ... ': ident , ... }
                                }
                                TokenKind::Identifier => {
                                    // we found an identifier, we'll consider we missed
                                    // the colon and use it as the field type

                                    // struct ident { ... , ident : ... 'ident , ... }
                                    self.lexer.push_next(token);
                                }
                                TokenKind::Comma => {
                                    // we found a comma, which means that the current
                                    // field was not completed. we can start over for the
                                    // next one

                                    // struct ident { ... , ident ... ', ... }
                                    expect_more = true;
                                    continue;
                                }
                                TokenKind::CloseCurlyBracket | TokenKind::Eof => {
                                    // we reached the end of the struct
                                    break token;
                                }
                                _ => unreachable!(),
                            }
                        }
                    }

                    // struct ident { ... , ident : 'ident , ... }

                    let token = self.lexer.next();
                    match token.kind() {
                        TokenKind::Identifier => {
                            // struct ident { ... , ident : 'ident , ... }
                            let ty = Identifier::new(
                                self.push_identifier(token.span()),
                                token.take_span(),
                            );
                            let field_span = ident.span().extend_to(ty.span());
                            fields.push(Field::new(ident, ty, field_span));
                        }
                        TokenKind::Comma => {
                            // we missed the type and got the comma. try to parse next field from
                            // here

                            // struct ident { ... , ident : ', ... }
                            report_unexpected_token!(self, token, [TokenKind::Identifier,]);
                            expect_more = true;
                            continue;
                        }
                        _ => {
                            // we missed the type
                            report_unexpected_token!(self, token, [TokenKind::Identifier,]);
                            self.take_until_one_of(vec![
                                TokenKind::Identifier,
                                TokenKind::Comma,
                                TokenKind::CloseCurlyBracket,
                            ]);

                            let token = self.lexer.next();
                            match token.kind() {
                                TokenKind::Identifier => {
                                    // struct ident { ... , ident : ... 'ident, ... }

                                    // we found the type, create the field
                                    let ty = Identifier::new(
                                        self.push_identifier(token.span()),
                                        token.take_span(),
                                    );
                                    let field_span = ident.span().extend_to(ty.span());
                                    fields.push(Field::new(ident, ty, field_span));
                                }
                                TokenKind::Comma => {
                                    // we found a comma, abort the current field and parse
                                    // the next one...

                                    // struct ident { ... , ident : ... ', ... }
                                    expect_more = true;
                                    continue;
                                }
                                TokenKind::CloseCurlyBracket | TokenKind::Eof => {
                                    // we reached the end of the struct
                                    break token;
                                }
                                _ => unreachable!(),
                            }
                        }
                    }

                    // finally, if the next token is a comma, we eat it and continue
                    // processing the next field
                    let token = self.lexer.peek();
                    if token.kind() == &TokenKind::Comma {
                        self.lexer.next();
                        expect_more = true
                    }
                }
                TokenKind::Eof => {
                    // we did not find either an identifier or a closing bracket.
                    if expect_more {
                        // we expected one mode field (we saw a comma), which means the next token
                        // would either be a closing bracket or an identifier
                        report_unexpected_token!(
                            self,
                            token,
                            [TokenKind::CloseCurlyBracket, TokenKind::Identifier,]
                        );
                    } else {
                        // we did not expect one mode field (we did not see a comma), which means
                        // the next token would either be a closing bracket or a comma
                        report_unexpected_token!(
                            self,
                            token,
                            [TokenKind::CloseCurlyBracket, TokenKind::Comma,]
                        );
                    }
                    break token;
                }
                _ => {
                    // we did find neither an identifier nor a closing bracket.
                    // we skip tokens to find one of them
                    report_unexpected_token!(
                        self,
                        token,
                        [TokenKind::CloseCurlyBracket, TokenKind::Identifier,]
                    );

                    // and we skip tokens to sync
                    self.take_until_one_of(vec![TokenKind::Comma, TokenKind::CloseCurlyBracket]);
                    let token = self.lexer.peek();
                    if token.kind() == &TokenKind::Comma {
                        self.lexer.next();
                        expect_more = true
                    }
                }
            }
        };

        let id = self.push_statement(
            StatementKind::Struct(identifier, fields),
            token_struct.take_span().extend_to(last_token.span()),
        );
        Some(&self.statements[id.id()])
    }

    /// Parses the following:
    /// ```
    /// 'expr
    /// ```
    fn parse_expression(&mut self) -> &Expression {
        self.parse_expression_with_precedence(Precedence::Lowest)
    }

    fn parse_expression_with_precedence(&mut self, precedence: Precedence) -> &Expression {
        let token = self.lexer.next();

        let mut expression = match token.kind() {
            TokenKind::If => {
                // self.expected.clear();
                self.parse_if_expression(token.span().clone()).id()
            }
            TokenKind::While => {
                // self.expected.clear();
                self.parse_while_expression(token.span().clone()).id()
            }
            TokenKind::Identifier => {
                // self.expected.clear();
                let identifier =
                    Identifier::new(self.push_identifier(token.span()), token.span().clone());

                let token = self.lexer.peek();

                match *token.kind() {
                    // ident '( ...
                    TokenKind::OpenParenthesis => self.parse_function_call(identifier).id(),
                    // ident '= ...
                    TokenKind::Equal => {
                        self.lexer.next();
                        let expression = self.parse_expression();
                        let span = identifier.span().extend_to(expression.span());
                        let expression = expression.id();
                        let ident_ref = self.push_identifier_ref(identifier);
                        self.push_expression(
                            ExpressionKind::Assignment(ident_ref, expression),
                            span,
                        )
                    }
                    _ => {
                        // ident '...
                        // we just take ident and leave the rest to the next step
                        let span = identifier.span().clone();

                        let ident_ref = self.push_identifier_ref(identifier);
                        let literal =
                            Literal::new(LiteralKind::Identifier(ident_ref), span.clone());

                        self.expected.insert(TokenKind::OpenParenthesis);
                        self.expected.insert(TokenKind::Equal);

                        self.push_expression(ExpressionKind::Literal(literal), span)
                    }
                }
            }
            TokenKind::Number(n) => {
                // self.expected.clear();
                let literal = Literal::new(LiteralKind::Number(*n), token.span().clone());
                self.push_expression(ExpressionKind::Literal(literal), token.span().clone())
            }
            TokenKind::Minus => {
                // self.expected.clear();
                let expression = self.parse_expression_with_precedence(Precedence::Prefix);
                let span = token.span().extend_to(expression.span());
                let expression = expression.id();
                self.push_expression(
                    ExpressionKind::Unary(
                        UnaryOperator::new(UnaryOperatorKind::Minus, token.span().clone()),
                        expression,
                    ),
                    span,
                )
            }
            TokenKind::True => {
                // self.expected.clear();
                self.push_expression(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Boolean(true),
                        token.span().clone(),
                    )),
                    token.span().clone(),
                )
            }
            TokenKind::False => {
                // self.expected.clear();
                self.push_expression(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Boolean(false),
                        token.span().clone(),
                    )),
                    token.span().clone(),
                )
            }
            TokenKind::OpenParenthesis => {
                // self.expected.clear();
                let open_loc = token.span();

                let expression = self.parse_expression().id();
                let token = self.lexer.next();
                let token = if token.kind() == &TokenKind::CloseParenthesis {
                    token
                } else {
                    let close_par = report_and_insert_missing_closing_token!(
                        self,
                        token,
                        TokenKind::CloseParenthesis,
                        TokenKind::OpenParenthesis,
                        open_loc
                    );
                    self.lexer.push_next(token);
                    close_par
                };

                // we need to alter the expression's span to account for open and close
                // parenthesis
                let expression = &mut self.expressions[expression.id()];
                expression.set_span(
                    open_loc
                        .extend_to(expression.span())
                        .extend_to(token.span()),
                );
                expression.id()
            }
            _ => {
                report_unexpected_token!(
                    self,
                    token,
                    [
                        TokenKind::Identifier,
                        TokenKind::Number(0),
                        TokenKind::Minus,
                        TokenKind::True,
                        TokenKind::False,
                        TokenKind::OpenParenthesis,
                        TokenKind::If,
                        TokenKind::While,
                    ]
                );
                // stuff that can legitimately come after an expression (or EOF because we need to
                // stop) - this probably means that the expression was actually missing.
                match token.kind() {
                    TokenKind::Eof
                    | TokenKind::Semicolon
                    | TokenKind::CloseParenthesis
                    | TokenKind::CloseCurlyBracket
                    | TokenKind::OpenCurlyBracket
                    | TokenKind::Comma
                    | TokenKind::EqualEqual
                    | TokenKind::ExclaimEqual
                    | TokenKind::Greater
                    | TokenKind::GreaterEqual
                    | TokenKind::Minus
                    | TokenKind::Plus
                    | TokenKind::Slash
                    | TokenKind::Smaller
                    | TokenKind::SmallerEqual
                    | TokenKind::Star => {
                        // insert a dummy expression
                        let span = Span::new(
                            token.span().line(),
                            token.span().column(),
                            token.span().start(),
                            0,
                        );
                        // let's keep parsing with the token that becomes legit thanks to the
                        // insertion of the dummy expression
                        self.lexer.push_next(token);
                        self.push_expression(ExpressionKind::Dummy, span)
                    }
                    _ => {
                        // try again after consuming the unexpected token
                        self.parse_expression_with_precedence(precedence).id()
                    }
                }
            }
        };

        while let Some(operator) = self.parse_binary_operator_with_higher_precedence(precedence) {
            expression = self.parse_infix_expression(expression, operator).id();
        }

        &self.expressions[expression.id()]
    }

    fn parse_binary_operator_with_higher_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Option<BinaryOperator> {
        let token = self.lexer.next();

        match token.kind() {
            TokenKind::EqualEqual => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Equality,
                    token.span().clone(),
                ))
            }
            TokenKind::ExclaimEqual => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::NonEquality,
                    token.span().clone(),
                ))
            }
            TokenKind::Greater => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::GreaterThan,
                    token.span().clone(),
                ))
            }
            TokenKind::GreaterEqual => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::GreaterThanOrEqualTo,
                    token.span().clone(),
                ))
            }
            TokenKind::Smaller => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::SmallerThan,
                    token.span().clone(),
                ))
            }
            TokenKind::SmallerEqual => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::SmallerThanOrEqualTo,
                    token.span().clone(),
                ))
            }
            TokenKind::Minus => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Subtraction,
                    token.span().clone(),
                ))
            }
            TokenKind::Plus => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Addition,
                    token.span().clone(),
                ))
            }
            TokenKind::Slash => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Division,
                    token.span().clone(),
                ))
            }
            TokenKind::Star => {
                // self.expected.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Multiplication,
                    token.span().clone(),
                ))
            }
            _ => {
                self.expected.insert(TokenKind::EqualEqual);
                self.expected.insert(TokenKind::ExclaimEqual);
                self.expected.insert(TokenKind::Greater);
                self.expected.insert(TokenKind::GreaterEqual);
                self.expected.insert(TokenKind::Minus);
                self.expected.insert(TokenKind::Plus);
                self.expected.insert(TokenKind::Slash);
                self.expected.insert(TokenKind::Smaller);
                self.expected.insert(TokenKind::SmallerEqual);
                self.expected.insert(TokenKind::Star);
                None
            }
        }
        .and_then(|op| {
            if op.kind().precedence() > precedence {
                Some(op)
            } else {
                None
            }
        })
        .or_else(|| {
            // either token was not an operator or operator did not have high enough precedence...
            self.lexer.push_next(token);
            None
        })
    }

    fn parse_infix_expression(&mut self, left: ExprId, operator: BinaryOperator) -> &Expression {
        let left_span = self.expressions[left.id()].span().clone();

        let right = self.parse_expression_with_precedence(operator.kind().precedence());
        let span = left_span.extend_to(right.span());

        let id = right.id();
        let id = self.push_expression(ExpressionKind::Binary(left, operator, id), span);

        &self.expressions[id.id()]
    }

    /// Parses the following (the `if` keyword is already consumed):
    /// ```
    /// if expr { expr ; ... } else if expr { expr ; } else { expr ; ... }
    /// ```
    fn parse_if_expression(&mut self, span: Span) -> &Expression {
        let mut full_span = span;

        // if 'expr { expr ; ... } ...
        let condition = self.parse_expression().id();

        // if expr '{ expr ; ... } ...
        let open_curly_bracket = self.lexer.next();
        let open_curly_bracket_span = open_curly_bracket.span().clone();

        if open_curly_bracket.kind() != &TokenKind::OpenCurlyBracket {
            report_unexpected_token!(
                self,
                open_curly_bracket,
                [
                    TokenKind::EqualEqual,
                    TokenKind::ExclaimEqual,
                    TokenKind::Greater,
                    TokenKind::GreaterEqual,
                    TokenKind::Minus,
                    TokenKind::Plus,
                    TokenKind::Slash,
                    TokenKind::Smaller,
                    TokenKind::SmallerEqual,
                    TokenKind::Star,
                    TokenKind::OpenCurlyBracket,
                ]
            );
            self.lexer.push_next(open_curly_bracket);
        }
        self.expected.clear();

        let (true_statements, true_statements_span) =
            self.parse_statements(&open_curly_bracket_span);

        let true_expression_span = open_curly_bracket_span.extend_to(&true_statements_span);
        full_span = full_span.extend_to(&true_expression_span);

        let true_expr_id =
            self.push_expression(ExpressionKind::Block(true_statements), true_expression_span);

        // ... 'else if expr { expr ; ... } else { expr ; ... }
        let false_expr_id = if self.lexer.peek().kind() == &TokenKind::Else {
            let _else_token = self.lexer.next(); // we consume the else
            let token = self.lexer.next();
            let false_block = match token.kind() {
                TokenKind::If => {
                    // ... else 'if expr { expr ; ... } ...
                    let expression = self.parse_if_expression(token.span().clone());
                    let id = expression.id();
                    let span = expression.span().clone();
                    Some((
                        vec![self.push_statement(StatementKind::Expression(id), span.clone())],
                        span,
                    ))
                }
                // else '{ expr ; ... }
                TokenKind::OpenCurlyBracket => {
                    let (statements, statements_span) = self.parse_statements(token.span());
                    Some((statements, token.span().extend_to(&statements_span)))
                }
                _ => {
                    report_unexpected_token!(
                        self,
                        token,
                        [TokenKind::OpenCurlyBracket, TokenKind::If,]
                    );
                    self.take_until_one_of(vec![
                        TokenKind::CloseCurlyBracket,
                        TokenKind::Semicolon,
                    ]);
                    None
                }
            };

            match false_block {
                Some((false_statements, false_statements_span)) => {
                    full_span = full_span.extend_to(&false_statements_span);
                    Some(self.push_expression(
                        ExpressionKind::Block(false_statements),
                        false_statements_span,
                    ))
                }
                None => None,
            }
        } else {
            // if expr { expr ; ... } '
            None
        };

        let id = self.push_expression(
            ExpressionKind::If(condition, true_expr_id, false_expr_id),
            full_span,
        );

        &self.expressions[id.id()]
    }

    fn parse_while_expression(&mut self, span: Span) -> &Expression {
        // while 'expr { expr ; ... }
        let condition = self.parse_expression().id();
        let open_curly_bracket = self.lexer.next();
        let open_curly_bracket_span = open_curly_bracket.span().clone();

        if open_curly_bracket.kind() != &TokenKind::OpenCurlyBracket {
            report_unexpected_token!(
                self,
                open_curly_bracket,
                [
                    TokenKind::EqualEqual,
                    TokenKind::ExclaimEqual,
                    TokenKind::Greater,
                    TokenKind::GreaterEqual,
                    TokenKind::Minus,
                    TokenKind::Plus,
                    TokenKind::Slash,
                    TokenKind::Smaller,
                    TokenKind::SmallerEqual,
                    TokenKind::Star,
                    TokenKind::OpenCurlyBracket,
                ]
            );
            self.lexer.push_next(open_curly_bracket);
        }
        self.expected.clear();

        let (statements, statements_span) = self.parse_statements(&open_curly_bracket_span);

        let block_span = open_curly_bracket_span.extend_to(&statements_span);

        let expr_id = self.push_expression(ExpressionKind::Block(statements), block_span);

        let id = self.push_expression(
            ExpressionKind::While(condition, expr_id),
            span.extend_to(&statements_span),
        );
        &self.expressions[id.id()]
    }

    /// Parses the following:
    /// ```
    /// identifier ( expr , ... )
    /// ```
    fn parse_function_call(&mut self, identifier: Identifier) -> &Expression {
        // identifier '( expr , ... )
        let open_parenthesis_token = self.lexer.next();
        assert_eq!(open_parenthesis_token.kind(), &TokenKind::OpenParenthesis);

        let mut arguments = Vec::new();
        let mut comma_seen = true;

        let span = loop {
            let token = self.lexer.peek();
            match *token.kind() {
                TokenKind::CloseParenthesis => {
                    let token = self.lexer.next();
                    break identifier.span().extend_to(token.span());
                }
                TokenKind::Comma if !comma_seen => {
                    self.lexer.next();
                    comma_seen = true;
                }
                TokenKind::Comma if comma_seen => {
                    let token = self.lexer.next();
                    report_unexpected_token!(
                        self,
                        token,
                        [
                            TokenKind::CloseParenthesis,
                            TokenKind::Identifier,
                            TokenKind::Number(0),
                            TokenKind::Minus,
                            TokenKind::True,
                            TokenKind::False,
                            TokenKind::OpenParenthesis,
                            TokenKind::If,
                            TokenKind::While,
                        ]
                    );
                }
                _ if comma_seen => {
                    arguments.push(self.parse_expression().id());
                    comma_seen = false;
                }
                _ => {
                    if !comma_seen {
                        report_and_insert_missing_token!(self, token, TokenKind::Comma);
                    }
                    arguments.push(self.parse_expression().id());
                    comma_seen = false;
                }
            }
        };

        // identifier ( expr , ... ) '
        let ident_ref = self.push_identifier_ref(identifier);
        let id = self.push_expression(ExpressionKind::FunctionCall(ident_ref, arguments), span);
        &self.expressions[id.id()]
    }

    fn parse_semicolon(&mut self) -> Token {
        let token = self.lexer.peek();
        if token.kind() == &TokenKind::Semicolon {
            self.expected.clear();
            self.lexer.next()
        } else {
            let span = token.span().clone();
            report_unexpected_token!(self, token, [TokenKind::Semicolon,]);
            self.take_until_one_of(vec![TokenKind::Semicolon]);
            self.lexer.next(); // consume the semicolon, if it's there (otherwise, we have eof)
            Token::new(
                TokenKind::Semicolon,
                Span::new(span.line(), span.column(), span.start(), 0),
            )
        }
    }

    /// the returned span includes the closing }
    fn parse_statements(&mut self, open_curly_bracket_span: &Span) -> (Vec<StmtId>, Span) {
        let mut statements = Vec::new();
        loop {
            let token = self.lexer.peek();
            match token.kind() {
                TokenKind::CloseCurlyBracket => {
                    break;
                }
                _ => {
                    if let Some(statement) = self.parse_statement() {
                        statements.push(statement.id());
                    } else {
                        // we were not able to parse a statement, let's quit the loop
                        break;
                    }
                }
            }
        }

        let token = self.lexer.next();
        let span = token.span().clone();
        if token.kind() != &TokenKind::CloseCurlyBracket {
            report_and_insert_missing_closing_token!(
                self,
                token,
                TokenKind::CloseCurlyBracket,
                TokenKind::OpenCurlyBracket,
                open_curly_bracket_span
            );
        }

        // not the whole span, the last token's span, which is good enough as we only want to know
        // where the statements end
        (statements, span)
    }

    fn push_identifier(&mut self, span: &Span) -> IdentId {
        let ident = self.lexer.span(span);
        if let Some(id) = self.identifiers.get(ident) {
            *id
        } else {
            let id = IdentId::from(self.identifiers.len());
            self.identifiers.insert(ident.to_string(), id);
            id
        }
    }

    fn push_identifier_ref(&mut self, ident: Identifier) -> IdentRefId {
        let id = IdentRefId::from(self.identifier_refs.len());
        self.identifier_refs.push(IdentifierRef::new(id, ident));
        id
    }

    fn push_expression(&mut self, kind: ExpressionKind, span: Span) -> ExprId {
        let id = ExprId::from(self.expressions.len());
        self.expressions.push(Expression::new(id, kind, span));
        id
    }

    fn push_statement(&mut self, kind: StatementKind<Untyped, Unbound>, span: Span) -> StmtId {
        let id = StmtId::from(self.statements.len());
        self.statements.push(Statement::new(id, kind, span));
        id
    }

    /// Consumes tokens until one of supplied one is found. It does NOT consume it.
    /// Returns the amount of skipped tokens
    // todo should return the matched token
    fn take_until_one_of(&mut self, mut token_kinds: Vec<TokenKind>) -> usize {
        // todo handle case where we are in a ( or in a { block
        //  i.e. if in a `(a + ...` we want to take all until parenthesis?
        token_kinds.push(TokenKind::Eof);
        self.take_while(|k| !token_kinds.contains(k))
    }

    /// Consumes tokens while `f` returns `true`. It does NOT consume the last one (i.e. first one
    /// for which `f` returns `false`).
    /// Returns the amount of skipped tokens
    fn take_while<F>(&mut self, f: F) -> usize
    where
        F: Fn(&TokenKind) -> bool,
    {
        let mut skipped = 0;
        let mut token = self.lexer.peek();
        while f(token.kind()) {
            self.lexer.next();
            token = self.lexer.peek();
            skipped += 1;
        }
        skipped
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_debug_snapshot;

    macro_rules! test_syntax {
        ($name:ident => $src:expr) => {
            #[test]
            fn $name() {
                assert_debug_snapshot!(Parser::new(Lexer::new($src)).parse());
            }
        };
    }

    test_syntax!(expression_literal_number => "42");
    test_syntax!(expression_literal_identifier => "forty_two");
    test_syntax!(expression_literal_boolean => "true");
    test_syntax!(expression => "2 + 20 * 2");
    test_syntax!(binary_operator_minus => "43 - 1");
    test_syntax!(prefix_minus => "- 40 * 2");
    test_syntax!(let_statement => "let forty_two = 42;");
    test_syntax!(assignment => "forty_two = 42");
    test_syntax!(two_statements => "let forty_two = 42; forty_two;");
    test_syntax!(function_statement => "let times_two(a: number) = a * 2;");
    test_syntax!(function_statement_with_return_type => "let times_two(a: number): number = a * 2;");
    test_syntax!(function_statements => "let times_two(a: number) = { a * 2; }");
    test_syntax!(function_call => "times_two(21)");
    test_syntax!(ret => "ret 42;");
    test_syntax!(if_simple => "if true { 42; }");
    test_syntax!(if_else => "if true { 42; } else { 43; }");
    test_syntax!(if_else_if_else => "if true { 42; } else if false { 43; } else { 44; }");
    test_syntax!(while_loop => "while true { 42; }");
    test_syntax!(struct_valid_zero_field => "struct S { }");
    test_syntax!(struct_valid_one_field => "struct S { a: number }");
    test_syntax!(struct_valid_several_fields => "struct S { a: number, b: number }");
    test_syntax!(struct_valid_trailing_comma => "struct S { a: number, }");
    test_syntax!(err_expression_missing_right_parenthesis => "(42;");
    test_syntax!(err_expression_missing_right_parenthesis_eof => "(42");
    test_syntax!(err_expression_inserted_token_before_expression => "^42;");
    test_syntax!(err_expression_missing_token_at_eof => "1 + ");
    test_syntax!(err_expression_missing_token => "1 + ;");
    test_syntax!(err_let_missing_identifier => "let = 42;");
    test_syntax!(err_let_missing_equal => "let forty_two 42;");
    test_syntax!(err_let_missing_expression => "let forty_two = ;");
    test_syntax!(err_let_missing_semicolon => "let forty_two = 42");
    test_syntax!(err_let_fn_params_unwanted_comma => "let x(,n:i,,m:j,) = { }");
    test_syntax!(err_let_fn_params_invalid_token_in_parameters_list => "let x(if) = { }");
    test_syntax!(err_let_fn_params_missing_colon_before_type => "let f(n integer) = { }");
    test_syntax!(err_let_fn_params_missing_type => "let f(n:) = { }");
    test_syntax!(err_let_fn_params_missing_colon_and_type => "let f(n) = { }");
    test_syntax!(err_let_fn_eof_in_params => "let x(");
    test_syntax!(err_let_fn_missing_equal => "let x() { }");
    test_syntax!(err_operator_illegal => "41 $ 1;");
    test_syntax!(err_illegal_char_in_place_of_potential_operator => "41 $");
    test_syntax!(err_unexpected_token_in_place_of_potential_operator_or_method_call_or_equal => "f 4;");
    test_syntax!(err_if_missing_condition => "if { }");
    test_syntax!(err_if_missing_open_curly_bracket => "if true }");
    test_syntax!(err_if_missing_close_curly_bracket => "if true {");
    test_syntax!(err_if_unexpected_token_after_else => "if true { } else 42");
    test_syntax!(err_while_missing_condition => "while { }");
    test_syntax!(err_while_missing_open_curly_bracket => "while true }");
    test_syntax!(err_while_missing_close_curly_bracket => "while true {");
    test_syntax!(err_function_call_unwanted_comma => "f(42,,43);");
    test_syntax!(err_function_call_missing_comma => "f(42 43);");
    test_syntax!(err_struct_missing_name => "struct { }");
    test_syntax!(err_struct_missing_open_curly_one_field => "struct S a: number }");
    test_syntax!(err_struct_missing_open_curly_no_fields => "struct S }");
    test_syntax!(err_struct_missing_close_curly_one_field => "struct S { a: number");
    test_syntax!(err_struct_missing_close_curly_one_field_trailing_comma => "struct S { a: number,");
    test_syntax!(err_struct_missing_close_curly_no_fields => "struct S {");
    test_syntax!(err_struct_missing_first_field_name => "struct S { : number, b: number, c: number }");
    test_syntax!(err_struct_missing_second_field_name => "struct S { a: number, : number, c: number }");
    test_syntax!(err_struct_missing_third_field_name => "struct S { a: number, b: number, : number }");
    test_syntax!(err_struct_missing_first_field_colon => "struct S { a number, b: number, c: number }");
    test_syntax!(err_struct_missing_second_field_colon => "struct S { a: number, b number, c: number }");
    test_syntax!(err_struct_missing_third_field_colon => "struct S { a: number, b: number, c number }");
    test_syntax!(err_struct_missing_first_field_type => "struct S { a: , b: number, c: number }");
    test_syntax!(err_struct_missing_second_field_type => "struct S { a: number, b: , c: number }");
    test_syntax!(err_struct_missing_third_field_type => "struct S { a: number, b: number, c: }");
}
