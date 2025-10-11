use crate::annotation::Annotation;
use crate::expression::{ExpressionKind, Target};
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::lexer::{Lexer, PeekableLexer, TokenKind};
use crate::literal::{Literal, LiteralKind};
use crate::operators::{
    BinaryOperator, BinaryOperatorKind, Precedence, UnaryOperator, UnaryOperatorKind,
};
use crate::statement::{Field, Parameter, RetMode, Return, StatementKind, TypeDef, TypeDefKind};
use crate::CompilationUnit;
use std::borrow::Cow;
use std::collections::HashSet;
#[cfg(all(not(test), not(feature = "allow-any-root-kind")))]
use transmute_core::error::{Diagnostic, Level};
use transmute_core::ids::{id, ExprId, IdentId, IdentRefId, StmtId, TypeDefId};
use transmute_core::span::Span;

// todo:ux review how diagnostics work. some ideas:
//   - keep tokens in a list to reports the missing token, together with what token it is supposed
//     to close, even when other tokens can be expected. eg.: for `[a;` we can expect either `1`,
//     etc., or `]` which closes the `]`.
//   - the last expression cal "tell" what token can come after. eg.: for `a` we can accept `(`,
//     `+`, etc. but for `1` we cannot accept `(`.

type Expression = crate::expression::Expression;
type Statement = crate::statement::Statement;

pub struct Parser<'s, 'c> {
    lexer: PeekableLexer<'s>,
    compilation_unit: &'c mut CompilationUnit,
    parent_namespace: StmtId,
    potential_tokens: HashSet<ExpectedToken>,
    eof: bool,
}

#[cfg(feature = "debug-expected-token")]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ExpectedToken(TokenKind, &'static str, u32);

#[cfg(not(feature = "debug-expected-token"))]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
struct ExpectedToken(TokenKind);

impl ExpectedToken {
    #[cfg(feature = "debug-expected-token")]
    fn description(&self) -> Cow<'_, str> {
        Cow::from(format!("{} {}", self.0.description(), self.2))
    }

    #[cfg(not(feature = "debug-expected-token"))]
    fn description(&self) -> Cow<'_, str> {
        self.0.description()
    }
}

#[cfg(feature = "debug-expected-token")]
macro_rules! expected_token {
    ($token:expr) => {
        ExpectedToken($token, file!(), line!())
    };
}

#[cfg(not(feature = "debug-expected-token"))]
macro_rules! expected_token {
    ($token:expr) => {
        ExpectedToken($token)
    };
}

/// Reports an unexpected token, together with the tokens that were expected.
macro_rules! report_unexpected_token {
    ($self:ident, $token:ident, [$($expected:expr,)*]) => {
        if !$self.eof {
            for e in vec![$($expected),*] {
                $self.potential_tokens.insert(e);
            }
            let mut potential_tokens = $self
                .potential_tokens
                .iter()
                .collect::<Vec<_>>();
            potential_tokens.sort();
            let span = $token.span.clone();
            let token_desc = if matches!(&$token.kind, TokenKind::Identifier) {
                format!("{}({})", $token.kind.to_string(), $self.lexer.span(&span))
            } else {
                $token.kind.to_string()
            };
            $self.compilation_unit.diagnostics.report_err(
                format!(
                    "Unexpected {}, expected one of ({}) {}",
                    token_desc,
                    potential_tokens.len(),
                    potential_tokens
                        .into_iter()
                        .map(|e| e.description())
                        .collect::<Vec<Cow<'_, str>>>()
                        .join(", ")
                ),
                span,
                (file!(), line!()),
            );
        }

        if &$token.kind == &TokenKind::Eof {
            $self.eof = true;
        }

        $self.potential_tokens.clear();
    };
}

/// Reports a missing token, together with the token that was found instead. Requeue the token for
/// further processing.
macro_rules! report_missing_token_and_push_back {
    ($self:ident, $token:ident, [$($expected:expr,)*]) => {
        if !$self.eof {
            for e in vec![$($expected),*] {
                $self.potential_tokens.insert(e);
            }
            let mut potential_tokens = $self
                .potential_tokens
                .iter()
                .collect::<Vec<_>>();
            potential_tokens.sort();
            let token_desc = if matches!(&$token.kind, TokenKind::Identifier) {
                format!("{}({})", &$token.kind.to_string(), $self.lexer.span(&$token.span))
            } else {
                $token.kind.to_string()
            };
            $self.compilation_unit.diagnostics.report_err(
                format!(
                    "Unexpected {}, expected one of ({}) {}",
                    token_desc,
                    potential_tokens.len(),
                    potential_tokens
                        .into_iter()
                        .map(|e| e.description())
                        .collect::<Vec<Cow<'_, str>>>()
                        .join(", "),
                ),
                $token.span.clone(),
                (file!(), line!()),
            );
        }

        if &$token.kind == &TokenKind::Eof {
            $self.eof = true;
        }

        $self.lexer.push_next($token);
        $self.potential_tokens.clear();
    };
    ($self:ident, $token:ident, $expected:expr) => {
        if !$self.eof {
            $self.compilation_unit.diagnostics.report_err(
                format!(
                    "Expected {}, got {}",
                    $expected.description(),
                    &$token.kind.description()
                ),
                $token.span.clone(),
                (file!(), line!()),
            );
        }

        if &$token.kind == &TokenKind::Eof {
            $self.eof = true;
        }

        $self.lexer.push_next($token);
        $self.potential_tokens.clear();
    };
}

/// Reports a missing closing token, together with the information about what is the corresponding
/// opening token and the token that was found instead.
macro_rules! report_missing_closing_token {
    ($self:ident, $token:ident, $expected:expr, $open_token:expr, $open_span:expr) => {
        if !$self.eof {
            $self.compilation_unit.diagnostics.report_err(
                format!(
                    "Expected {} to close {} at {}:{}, got {}",
                    $expected.description(),
                    $open_token.description(),
                    $open_span.line,
                    $open_span.column,
                    $token.kind
                ),
                $token.span.clone(),
                (file!(), line!()),
            );
        }

        if &$token.kind == &TokenKind::Eof {
            $self.eof = true;
        }

        $self.potential_tokens.clear();
    };
}

impl<'s, 'c> Parser<'s, 'c> {
    pub fn new(
        compilation_unit: &'c mut CompilationUnit,
        parent_namespace: Option<StmtId>,
        lexer: Lexer<'s>,
    ) -> Self {
        Self {
            lexer: PeekableLexer::new(lexer, 1),
            parent_namespace: parent_namespace.unwrap_or_else(|| compilation_unit.root_namespace()),
            compilation_unit,
            potential_tokens: Default::default(),
            eof: false,
        }
    }

    pub fn parse(mut self) {
        let (namespace, mut statements) = self
            .compilation_unit
            .statements
            .remove(self.parent_namespace)
            .map(|stmt| match stmt.kind {
                StatementKind::Namespace(identifier, input, statements) => {
                    ((stmt.id, stmt.span, identifier, input), statements)
                }
                _ => panic!("Namespace expected, got {stmt:?}"),
            })
            .expect("Parent namespace exists");

        while let Some(statement) = self.parse_statement() {
            match &statement.kind {
                StatementKind::LetFn(..)
                | StatementKind::Struct(..)
                | StatementKind::Annotation(..)
                | StatementKind::Use(..)
                | StatementKind::Namespace(..) => statements.push(statement.id),
                StatementKind::Expression(..) | StatementKind::Let(..) | StatementKind::Ret(..) => {
                    // when testing we are fine with having any statement as top level... while
                    // not perfect, this eases things a lot
                    #[cfg(any(test, feature = "allow-any-root-kind"))]
                    statements.push(statement.id);

                    #[cfg(all(not(test), not(feature = "allow-any-root-kind")))]
                    {
                        let span = statement.span.clone();
                        self.compilation_unit.diagnostics.push(Diagnostic::new(
                            "Only use, namespaces, functions and structs are allowed at top level",
                            span,
                            Level::Error,
                            (file!(), line!()),
                        ))
                    }
                }
            }
        }

        let (stmt_id, span, identifier, input) = namespace;
        self.compilation_unit.statements.insert(
            stmt_id,
            Statement {
                id: stmt_id,
                kind: StatementKind::Namespace(identifier, input, statements),
                span,
            },
        );

        self.compilation_unit
            .diagnostics
            .append(self.lexer.diagnostics());
    }

    /// Parses the following:
    /// ```raw
    /// 'let ident = expr ;
    /// '@annotation let ident ( expr , ... ) = expr ;
    /// '@annotation let ident ( expr , ... ) = { expr ; ... }
    /// `@annotation struct ident { ident : ident , ... }`
    /// 'expr ;
    /// 'ret expr ;
    /// 'annotation ident ;
    /// ```
    fn parse_statement(&mut self) -> Option<&Statement> {
        let mut token = self.lexer.peek();

        while token.kind == TokenKind::Semicolon {
            let _semicolon = self.lexer.next_token();
            self.potential_tokens.clear();
            token = self.lexer.peek();
        }

        if token.kind == TokenKind::Eof || token.kind == TokenKind::CloseCurlyBracket {
            return None;
        }

        let mut annotations = Vec::new();
        while let Some(annotation) = self.parse_annotation() {
            annotations.push(annotation);
        }

        let token = self.lexer.peek();
        match &token.kind {
            TokenKind::Let => {
                let let_token = self.lexer.next_token();
                self.potential_tokens.clear();
                let identifier_token = self.lexer.next_token();
                let identifier = match &identifier_token.kind {
                    TokenKind::Identifier => Identifier::new(
                        self.push_identifier(&identifier_token.span),
                        identifier_token.span.clone(),
                    ),
                    _ => {
                        report_unexpected_token!(
                            self,
                            identifier_token,
                            [expected_token!(TokenKind::Identifier),]
                        );
                        self.take_until_one_of(vec![TokenKind::Semicolon]);
                        return None;
                    }
                };

                let token = self.lexer.peek();

                if token.kind == TokenKind::OpenParenthesis {
                    // let ident '( expr , ... ) = expr ;
                    return self.parse_function(&let_token.span, annotations, identifier);
                }

                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on non `let`-function statements",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                // let ident '= expr ;
                let token = self.lexer.next_token();
                if token.kind != TokenKind::Equal {
                    report_missing_token_and_push_back!(self, token, TokenKind::Equal);
                }

                // let ident = 'expr ;
                let expression = self.parse_expression(true, false).0.id;

                // let ident = expr ';
                let semicolon_span = self.parse_semicolon();

                let span = let_token.span.extend_to(&semicolon_span);

                let id = self.push_statement(StatementKind::Let(identifier, expression), span);
                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::Ret => {
                let ret_token = self.lexer.next_token();
                self.potential_tokens.clear();
                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on `ret` statements",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                let expression = match self.lexer.peek().kind {
                    TokenKind::Semicolon => None,
                    _ => {
                        self.potential_tokens
                            .insert(expected_token!(TokenKind::Semicolon));
                        Some(self.parse_expression(true, false).0.id)
                    }
                };

                let semicolon_span = self.parse_semicolon();
                let span = ret_token.span.extend_to(&semicolon_span);

                let id =
                    self.push_statement(StatementKind::Ret(expression, RetMode::Explicit), span);
                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::If | TokenKind::While => {
                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on expressions",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                let (expression, need_semi) = self.parse_expression(true, true);
                let span = expression.span.extend_to(&expression.span);
                let id = expression.id;
                let id = self.push_statement(StatementKind::Expression(id), span);

                if need_semi {
                    self.parse_semicolon();
                }

                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::False
            | TokenKind::Identifier
            | TokenKind::Minus
            | TokenKind::Number(_)
            | TokenKind::String(_)
            | TokenKind::OpenParenthesis
            | TokenKind::OpenBracket
            | TokenKind::True => {
                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on expressions",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                let expression = self.parse_expression(true, true).0;
                let span = expression.span.clone();
                let expression = expression.id;

                let semicolon_span = self.parse_semicolon();
                let span = span.extend_to(&semicolon_span);

                let id = self.push_statement(StatementKind::Expression(expression), span);
                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::Struct => self.parse_struct(annotations),
            TokenKind::Annotation => {
                // todo:feature remove the possibility to define annotations inside functions
                let annotation_token = self.lexer.next_token();
                self.potential_tokens.clear();

                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on annotations",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                let identifier_token = self.lexer.next_token();
                let identifier = match &identifier_token.kind {
                    TokenKind::Identifier => Identifier::new(
                        self.push_identifier(&identifier_token.span),
                        identifier_token.span.clone(),
                    ),
                    _ => {
                        report_unexpected_token!(
                            self,
                            identifier_token,
                            [expected_token!(TokenKind::Identifier),]
                        );
                        self.take_until_one_of(vec![TokenKind::Semicolon]);
                        return None;
                    }
                };

                let semicolon_span = self.parse_semicolon();

                let span = annotation_token.span.extend_to(&semicolon_span);

                let id = self.push_statement(StatementKind::Annotation(identifier), span);
                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::Use => {
                let use_token = self.lexer.next_token();
                self.potential_tokens.clear();

                if !annotations.is_empty() {
                    self.compilation_unit.diagnostics.report_err(
                        "Annotations not supported on use",
                        annotations
                            .first()?
                            .span
                            .extend_to(&annotations.last()?.span),
                        (file!(), line!()),
                    );
                }

                let mut fq_identifier = Vec::new();
                loop {
                    let identifier_token = self.lexer.next_token();
                    let identifier = match &identifier_token.kind {
                        TokenKind::Identifier => Identifier::new(
                            self.push_identifier(&identifier_token.span),
                            identifier_token.span.clone(),
                        ),
                        _ => {
                            report_unexpected_token!(
                                self,
                                identifier_token,
                                [expected_token!(TokenKind::Identifier),]
                            );
                            self.lexer.push_next(identifier_token);
                            return None;
                        }
                    };
                    fq_identifier.push(identifier);

                    if !matches!(self.lexer.peek().kind, TokenKind::Dot) {
                        break;
                    }
                    // consume the `.`
                    self.lexer.next_token();
                }

                let ident_ref_ids = fq_identifier
                    .into_iter()
                    .map(|identifier| self.push_identifier_ref(identifier))
                    .collect::<Vec<_>>();

                let semicolon_span = self.parse_semicolon();

                let span = use_token.span.extend_to(&semicolon_span);

                let id = self.push_statement(StatementKind::Use(ident_ref_ids), span);
                Some(&self.compilation_unit.statements[id])
            }
            TokenKind::Namespace => {
                // todo:feature remove the possibility to define namespaces inside functions
                let mod_token = self.lexer.next_token();
                self.potential_tokens.clear();

                let identifier_token = self.lexer.next_token();
                let identifier = match &identifier_token.kind {
                    TokenKind::Identifier => Identifier::new(
                        self.push_identifier(&identifier_token.span),
                        identifier_token.span.clone(),
                    ),
                    _ => {
                        report_unexpected_token!(
                            self,
                            identifier_token,
                            [expected_token!(TokenKind::Identifier),]
                        );
                        self.take_until_one_of(vec![TokenKind::Semicolon]);
                        return None;
                    }
                };

                let next = self.lexer.next_token();
                let (span, statements, from_file) = match next.kind {
                    TokenKind::OpenCurlyBracket => {
                        let (statements, span) = self.parse_statements(&next.span);
                        // parse_statements consumes the closing bracket
                        (span, statements, false)
                    }
                    TokenKind::Semicolon => {
                        (mod_token.span.extend_to(&next.span), Vec::new(), true)
                    }
                    _ => {
                        report_unexpected_token!(
                            self,
                            next,
                            [
                                expected_token!(TokenKind::Semicolon),
                                expected_token!(TokenKind::OpenCurlyBracket),
                            ]
                        );
                        self.take_until_one_of(vec![
                            TokenKind::Semicolon,
                            TokenKind::CloseCurlyBracket,
                        ]);
                        return None;
                    }
                };

                let id = self.push_statement(
                    StatementKind::Namespace(identifier, self.lexer.input_id(), statements),
                    span,
                );

                if from_file {
                    self.compilation_unit.namespaces.push(id);
                }

                Some(&self.compilation_unit.statements[id])
            }
            _ => {
                let token = self.lexer.next_token();
                report_unexpected_token!(
                    self,
                    token,
                    [
                        expected_token!(TokenKind::Identifier),
                        expected_token!(TokenKind::Number(0)),
                        expected_token!(TokenKind::Minus),
                        expected_token!(TokenKind::True),
                        expected_token!(TokenKind::False),
                        expected_token!(TokenKind::OpenParenthesis),
                        expected_token!(TokenKind::OpenBracket),
                        expected_token!(TokenKind::Let),
                        expected_token!(TokenKind::Ret),
                        expected_token!(TokenKind::If),
                        expected_token!(TokenKind::While),
                    ]
                );
                match &token.kind {
                    TokenKind::Eof => None,
                    _ => {
                        // try again after having consumed the unexpected token
                        self.parse_statement()
                    }
                }
            }
        }
    }

    fn parse_annotation(&mut self) -> Option<Annotation> {
        if matches!(self.lexer.peek().kind, TokenKind::At) {
            let at_token = self.lexer.next_token();

            let mut fq_identifier = Vec::new();
            loop {
                let identifier_token = self.lexer.next_token();
                let identifier = match &identifier_token.kind {
                    TokenKind::Identifier => Identifier::new(
                        self.push_identifier(&identifier_token.span),
                        identifier_token.span.clone(),
                    ),
                    _ => {
                        report_unexpected_token!(
                            self,
                            identifier_token,
                            [expected_token!(TokenKind::Identifier),]
                        );
                        self.lexer.push_next(identifier_token);
                        return None;
                    }
                };
                fq_identifier.push(identifier);

                if !matches!(self.lexer.peek().kind, TokenKind::Dot) {
                    break;
                }
                // consume the `.`
                self.lexer.next_token();
            }

            let span = at_token.span.extend_to(&fq_identifier.last().unwrap().span);
            let ident_ref_ids = fq_identifier
                .into_iter()
                .map(|identifier| self.push_identifier_ref(identifier))
                .collect::<Vec<_>>();

            return Some(Annotation {
                ident_ref_ids,
                span,
            });
        }

        None
    }

    /// Parses the following:
    /// ```raw
    /// let ident '( param , ... ): type = expr ;
    /// let ident '( param , ... ): type = { expr ; ... } ;
    /// ```
    fn parse_function(
        &mut self,
        span: &Span,
        annotations: Vec<Annotation>,
        identifier: Identifier,
    ) -> Option<&Statement> {
        // let name '( param , ... ): type = expr ;
        let open_parenthesis_token = self.lexer.next_token();
        self.potential_tokens.clear();

        assert_eq!(open_parenthesis_token.kind, TokenKind::OpenParenthesis);

        let mut parameters = Vec::new();
        let mut next = TokenKind::Identifier;

        loop {
            let token = self.lexer.next_token();
            match &token.kind {
                TokenKind::CloseParenthesis => {
                    self.potential_tokens.clear();
                    break;
                }
                TokenKind::Comma if next == TokenKind::Comma => {
                    self.potential_tokens.clear();
                    self.potential_tokens
                        .insert(expected_token!(TokenKind::Identifier));
                    next = TokenKind::Identifier;
                }
                TokenKind::Identifier if next == TokenKind::Identifier => {
                    self.potential_tokens.clear();

                    let ident =
                        Identifier::new(self.push_identifier(&token.span), token.span.clone());

                    let colon = self.lexer.next_token();
                    let type_def_id = if !matches!(colon.kind, TokenKind::Colon) {
                        report_missing_token_and_push_back!(self, colon, TokenKind::Colon);
                        self.parse_type(false)
                    } else {
                        self.parse_type(true)
                    };

                    let parameter_span = ident
                        .span
                        .extend_to(&self.compilation_unit.type_defs[type_def_id].span);

                    parameters.push(Parameter::new(ident, type_def_id, parameter_span));

                    self.potential_tokens
                        .insert(expected_token!(TokenKind::Comma));

                    next = TokenKind::Comma;
                }
                TokenKind::Eof => {
                    report_unexpected_token!(
                        self,
                        token,
                        [
                            expected_token!(next),
                            expected_token!(TokenKind::CloseParenthesis),
                        ]
                    );
                    return None;
                }
                _ => {
                    report_unexpected_token!(
                        self,
                        token,
                        [expected_token!(TokenKind::CloseParenthesis),]
                    );
                    self.take_until_one_of(vec![
                        TokenKind::Identifier,
                        TokenKind::CloseParenthesis,
                    ]);
                }
            }
        }

        let ty = if self.lexer.peek().kind == TokenKind::Colon {
            self.lexer.next_token();
            self.potential_tokens.clear();
            Return::some(self.parse_type(true))
        } else {
            Return::none()
        };

        // let name ( param , ... ): type '= expr ;
        let token = self.lexer.next_token();
        match token.kind {
            TokenKind::Equal => {
                self.potential_tokens.clear();
            }
            TokenKind::OpenCurlyBracket => {
                self.lexer.push_next(token);
            }
            _ => {
                report_missing_token_and_push_back!(
                    self,
                    token,
                    [
                        expected_token!(TokenKind::Equal),
                        expected_token!(TokenKind::OpenCurlyBracket),
                    ]
                );
            }
        }

        let (expr_id, end_span) = if self.lexer.peek().kind == TokenKind::OpenCurlyBracket {
            // let name ( param , ... ): type = '{ expr ; ... }
            let open_curly_bracket = self.lexer.next_token();
            self.potential_tokens.clear();

            let (statements, statements_span) = self.parse_statements(&open_curly_bracket.span);

            (
                self.push_expression(
                    ExpressionKind::Block(statements),
                    open_curly_bracket.span.extend_to(&statements_span),
                ),
                statements_span,
            )
        } else {
            // let name ( param , ... ): type = 'expr ;
            let expression = self.parse_expression(true, false).0;
            let expr_id = expression.id;
            let expr_span = expression.span.clone();

            let semicolon_span = self.parse_semicolon();
            let end_span = expr_span.extend_to(&semicolon_span);

            let stmt_id = self.push_statement(StatementKind::Expression(expr_id), end_span.clone());

            (
                self.push_expression(ExpressionKind::Block(vec![stmt_id]), end_span.clone()),
                end_span,
            )
        };

        let stmt_id = self.push_statement(
            StatementKind::LetFn(identifier, annotations, parameters, ty, expr_id),
            span.extend_to(&end_span),
        );

        Some(&self.compilation_unit.statements[stmt_id])
    }

    fn parse_type(&mut self, mut report_err: bool) -> TypeDefId {
        let token = self.lexer.next_token();
        match &token.kind {
            TokenKind::Identifier => {
                let mut token = token;
                let mut fq_identifier = Vec::new();
                loop {
                    let identifier = match &token.kind {
                        TokenKind::Identifier => {
                            Identifier::new(self.push_identifier(&token.span), token.span.clone())
                        }
                        _ => {
                            report_unexpected_token!(
                                self,
                                token,
                                [expected_token!(TokenKind::Identifier),]
                            );
                            self.lexer.push_next(token);
                            break;
                        }
                    };
                    fq_identifier.push(identifier);

                    if !matches!(self.lexer.peek().kind, TokenKind::Dot) {
                        break;
                    }
                    // consume the `.`
                    self.lexer.next_token();
                    token = self.lexer.next_token();
                }

                let span = fq_identifier
                    .first()
                    .unwrap()
                    .span
                    .extend_to(&fq_identifier.last().unwrap().span);
                let ident_ref_ids = fq_identifier
                    .into_iter()
                    .map(|identifier| self.push_identifier_ref(identifier))
                    .collect::<Vec<_>>();

                let type_def_id = self.compilation_unit.type_defs.create();
                self.compilation_unit.type_defs.insert(
                    type_def_id,
                    TypeDef {
                        kind: TypeDefKind::Simple(ident_ref_ids),
                        span,
                    },
                );

                type_def_id
            }
            TokenKind::OpenBracket => {
                let base = self.parse_type(true);

                let semi = self.lexer.next_token();

                if !matches!(semi.kind, TokenKind::Semicolon) {
                    report_unexpected_token!(self, semi, [expected_token!(TokenKind::Semicolon),]);
                    report_err = false;
                    self.lexer.push_next(semi);
                }

                let len = self.lexer.next_token();
                let type_def_kind = if let TokenKind::Number(len) = len.kind {
                    TypeDefKind::Array(base, len as usize)
                } else {
                    if report_err {
                        report_unexpected_token!(
                            self,
                            len,
                            [expected_token!(TokenKind::Number(0)),]
                        );
                    }
                    report_err = false;
                    self.lexer.push_next(len);
                    TypeDefKind::Dummy
                };

                let close_bracket = self.lexer.next_token();
                if !matches!(close_bracket.kind, TokenKind::CloseBracket) {
                    if report_err {
                        report_unexpected_token!(
                            self,
                            close_bracket,
                            [expected_token!(TokenKind::CloseBracket),]
                        );
                    }

                    self.lexer.push_next(close_bracket);
                    self.take_until_one_of(vec![
                        TokenKind::CloseBracket,
                        TokenKind::Semicolon,
                        TokenKind::OpenCurlyBracket,
                        TokenKind::CloseCurlyBracket,
                        TokenKind::Comma,
                        TokenKind::OpenParenthesis,
                        TokenKind::CloseParenthesis,
                    ]);

                    let type_def_id = self.compilation_unit.type_defs.create();
                    self.compilation_unit.type_defs.insert(
                        type_def_id,
                        TypeDef {
                            kind: TypeDefKind::Dummy,
                            span: token.span,
                        },
                    );
                    return type_def_id;
                }

                let type_def_id = self.compilation_unit.type_defs.create();
                self.compilation_unit.type_defs.insert(
                    type_def_id,
                    TypeDef {
                        kind: type_def_kind,
                        span: token.span.extend_to(&close_bracket.span),
                    },
                );
                type_def_id
            }
            _ => {
                if report_err {
                    report_unexpected_token!(
                        self,
                        token,
                        [
                            expected_token!(TokenKind::Identifier),
                            expected_token!(TokenKind::OpenBracket),
                        ]
                    );
                }

                self.compilation_unit.type_defs.push(TypeDef {
                    kind: TypeDefKind::Dummy,
                    span: Span::new(
                        self.lexer.input_id(),
                        token.span.line,
                        token.span.column,
                        token.span.start,
                        0,
                    ),
                });

                self.lexer.push_next(token);

                TypeDefId::from(self.compilation_unit.type_defs.len() - 1)
            }
        }
    }

    fn parse_struct(&mut self, annotations: Vec<Annotation>) -> Option<&Statement> {
        // 'struct ident < type , ... > { ident : ident , ... }
        let token_struct = self.lexer.next_token();
        let identifier_token = self.lexer.next_token();
        let identifier = match &identifier_token.kind {
            TokenKind::Identifier => Identifier::new(
                self.push_identifier(&identifier_token.span),
                identifier_token.span.clone(),
            ),
            _ => {
                report_unexpected_token!(
                    self,
                    identifier_token,
                    [expected_token!(TokenKind::Identifier),]
                );
                self.take_until_one_of(vec![TokenKind::CloseCurlyBracket, TokenKind::Semicolon]);
                return None;
            }
        };

        // struct ident '< type , ... > { ident : ident , ... }
        let token = self.lexer.peek();

        let type_parameters = if matches!(token.kind, TokenKind::Smaller) {
            let open_span = token.span.clone();
            self.lexer.next_token();
            // struct ident < 'type , ... > { ident : ident , ... }
            let mut type_parameters = vec![];
            let mut expect_type = true;

            loop {
                let token = self.lexer.next_token();

                match &token.kind {
                    TokenKind::Greater => {
                        // struct ident < ... '> { ... }
                        break;
                    }
                    TokenKind::Identifier => {
                        if !expect_type {
                            // we did not finish the previous type parameter with a comma but got
                            // the identifier of a new one. report the error and continue as if the
                            // comma was there
                            report_unexpected_token!(
                                self,
                                token,
                                [
                                    expected_token!(TokenKind::Comma),
                                    expected_token!(TokenKind::Greater),
                                ]
                            );
                        }

                        let ident =
                            Identifier::new(self.push_identifier(&token.span), token.span.clone());
                        type_parameters.push(ident);

                        expect_type = false;
                    }
                    TokenKind::Comma => {
                        if expect_type {
                            // we already read a comma, and we got another one. report the error
                            // and continue as if the comma was not there
                            report_unexpected_token!(
                                self,
                                token,
                                [
                                    expected_token!(TokenKind::Identifier),
                                    expected_token!(TokenKind::Greater),
                                ]
                            );
                        }

                        expect_type = true;
                    }
                    _ => {
                        // we got some random token... let's see if next one is an opening curly
                        // bracket
                        // let next_token = self.lexer.next_token();
                        if matches!(&token.kind, TokenKind::OpenCurlyBracket) {
                            // report the error and pretend we got the >
                            report_missing_closing_token!(
                                self,
                                token,
                                TokenKind::Greater,
                                TokenKind::Smaller,
                                open_span
                            );
                            self.lexer.push_next(token);
                        } else if expect_type {
                            report_unexpected_token!(
                                self,
                                token,
                                [
                                    expected_token!(TokenKind::Greater),
                                    expected_token!(TokenKind::Identifier),
                                ]
                            );
                        } else {
                            report_unexpected_token!(
                                self,
                                token,
                                [
                                    expected_token!(TokenKind::Greater),
                                    expected_token!(TokenKind::Comma),
                                ]
                            );
                        }

                        break;
                    }
                }
            }

            type_parameters
        } else {
            vec![]
        };

        let token = self.lexer.next_token();

        if !matches!(token.kind, TokenKind::OpenCurlyBracket) {
            if matches!(self.lexer.peek().kind, TokenKind::OpenCurlyBracket) {
                report_unexpected_token!(
                    self,
                    token,
                    [expected_token!(TokenKind::OpenCurlyBracket),]
                );
                self.lexer.next_token();
            } else {
                report_missing_token_and_push_back!(self, token, TokenKind::OpenCurlyBracket);
            }
        }

        let mut fields = Vec::new();
        let mut expect_more = true;

        let last_token = loop {
            // struct ident { ... , 'ident : ident , ... }
            let token = self.lexer.next_token();
            match &token.kind {
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
                            [
                                expected_token!(TokenKind::Colon),
                                expected_token!(TokenKind::CloseCurlyBracket),
                            ]
                        );
                    }

                    let ident =
                        Identifier::new(self.push_identifier(&token.span), token.span.clone());
                    expect_more = false;

                    // struct ident { ... , ident ': ident , ... }

                    let token = self.lexer.next_token();
                    match &token.kind {
                        TokenKind::Colon => {}
                        _ => {
                            // we missed the colon
                            report_unexpected_token!(
                                self,
                                token,
                                [expected_token!(TokenKind::Colon),]
                            );
                            self.take_until_one_of(vec![
                                TokenKind::Colon,
                                TokenKind::Identifier,
                                TokenKind::Comma,
                                TokenKind::CloseCurlyBracket,
                            ]);

                            let token = self.lexer.next_token();
                            match &token.kind {
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

                    let type_def_id = self.parse_type(true);
                    let field_span = ident
                        .span
                        .extend_to(&self.compilation_unit.type_defs[type_def_id].span);

                    fields.push(Field::new(ident, type_def_id, field_span));

                    // finally, if the next token is a comma, we eat it and continue
                    // processing the next field
                    let token = self.lexer.peek();
                    if token.kind == TokenKind::Comma {
                        self.lexer.next_token();
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
                            [
                                expected_token!(TokenKind::CloseCurlyBracket),
                                expected_token!(TokenKind::Identifier),
                            ]
                        );
                    } else {
                        // we did not expect one mode field (we did not see a comma), which means
                        // the next token would either be a closing bracket or a comma
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(TokenKind::CloseCurlyBracket),
                                expected_token!(TokenKind::Comma),
                            ]
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
                        [
                            expected_token!(TokenKind::CloseCurlyBracket),
                            expected_token!(TokenKind::Identifier),
                        ]
                    );

                    // and we skip tokens to sync
                    self.take_until_one_of(vec![TokenKind::Comma, TokenKind::CloseCurlyBracket]);
                    let token = self.lexer.peek();
                    if token.kind == TokenKind::Comma {
                        self.lexer.next_token();
                        expect_more = true
                    }
                }
            }
        };

        let stmt_id = self.push_statement(
            StatementKind::Struct(identifier, annotations, type_parameters, fields),
            token_struct.span.extend_to(&last_token.span),
        );
        Some(&self.compilation_unit.statements[stmt_id])
    }

    /// Parses the following:
    /// ```raw
    /// 'expr
    /// ```
    ///
    /// If `allow_struct` is set to `true`, a struct instantiation expression is allowed. If
    /// `allow_assignment` is set to `true` an assignment expression is allowed.
    ///
    /// Returns an `Expression` and a `bool` indicating whether a semicolon is required as the next
    /// token.
    fn parse_expression(
        &mut self,
        allow_struct: bool,
        allow_assignment: bool,
    ) -> (&Expression, bool) {
        self.parse_expression_with_precedence(Precedence::Lowest, allow_struct, allow_assignment)
    }

    fn parse_expression_with_precedence(
        &mut self,
        precedence: Precedence,
        allow_struct: bool,
        mut allow_assignment: bool,
    ) -> (&Expression, bool) {
        let token = self.lexer.next_token();

        let mut expr_id = match token.kind {
            TokenKind::If => {
                self.potential_tokens.clear();
                self.parse_if_expression(token.span.clone()).id
            }
            TokenKind::While => {
                self.potential_tokens.clear();
                self.parse_while_expression(token.span.clone()).id
            }
            TokenKind::Identifier => {
                self.potential_tokens.clear();

                let identifier =
                    Identifier::new(self.push_identifier(&token.span), token.span.clone());

                let mut generic_types = match self.lexer.peek().kind {
                    TokenKind::Exclaim => {
                        // identifier '! < ... > ...
                        let span = self.lexer.next_token().span;
                        let mut generic_types = vec![];

                        let angle_bracket = self.lexer.next_token();
                        if !matches!(angle_bracket.kind, TokenKind::Smaller) {
                            report_missing_token_and_push_back!(self, token, TokenKind::Smaller);
                        }

                        let mut expect_type = true;
                        loop {
                            let token = self.lexer.next_token();
                            match token.kind {
                                TokenKind::Greater => {
                                    span.extend_to(&token.span);
                                    break;
                                }
                                TokenKind::Comma => {
                                    if expect_type {
                                        report_unexpected_token!(
                                            self,
                                            token,
                                            [
                                                expected_token!(TokenKind::Identifier),
                                                expected_token!(TokenKind::OpenBracket),
                                            ]
                                        );
                                    }
                                    expect_type = true;
                                }
                                TokenKind::OpenCurlyBracket | TokenKind::Semicolon => {
                                    span.extend_to(&token.span);
                                    report_missing_closing_token!(
                                        self,
                                        token,
                                        TokenKind::Greater,
                                        TokenKind::Smaller,
                                        span
                                    );
                                    self.lexer.push_next(token);
                                    break;
                                }
                                _ if expect_type => {
                                    self.lexer.push_next(token);
                                    generic_types.push(self.parse_type(true));
                                    expect_type = false;
                                }
                                _ => {
                                    report_unexpected_token!(
                                        self,
                                        token,
                                        [
                                            expected_token!(TokenKind::Comma),
                                            expected_token!(TokenKind::Greater),
                                        ]
                                    );
                                }
                            }
                        }

                        Some((span, generic_types))
                    }
                    _ => None,
                };

                match &self.lexer.peek().kind {
                    // ident!<t...> '{ ...
                    TokenKind::OpenCurlyBracket if allow_struct => {
                        allow_assignment = false;
                        self.parse_struct_instantiation(
                            identifier,
                            generic_types
                                .take()
                                .map(|(_, type_defs_ids)| type_defs_ids)
                                .unwrap_or_default(),
                        )
                    }
                    // ident!<t...> '. f ( ) -> loop
                    // ident!<t...> '[ 1 ]   -> loop
                    // ident!<t...> '( )     -> loop
                    _ => {
                        if allow_struct {
                            self.potential_tokens
                                .insert(expected_token!(TokenKind::OpenCurlyBracket));
                        }

                        // ident '...
                        // we just take ident and leave the rest to the next step
                        let span = identifier.span.clone();

                        let ident_ref_id = self.push_identifier_ref(identifier);
                        let literal =
                            Literal::new(LiteralKind::Identifier(ident_ref_id), span.clone());

                        self.push_expression(ExpressionKind::Literal(literal), span)
                    }
                }
            }
            TokenKind::Number(n) => {
                self.potential_tokens.clear();
                let literal = Literal::new(LiteralKind::Number(n), token.span.clone());
                self.push_expression(ExpressionKind::Literal(literal), token.span.clone())
            }
            TokenKind::String(str) => {
                self.potential_tokens.clear();
                let literal = Literal::new(LiteralKind::String(str), token.span.clone());
                self.push_expression(ExpressionKind::Literal(literal), token.span.clone())
            }
            TokenKind::Minus => {
                self.potential_tokens.clear();
                let (expression, _) = self.parse_expression_with_precedence(
                    Precedence::Prefix,
                    allow_struct,
                    allow_assignment,
                );
                let span = token.span.extend_to(&expression.span);
                let expression = expression.id;
                self.push_expression(
                    ExpressionKind::Unary(
                        UnaryOperator::new(UnaryOperatorKind::Minus, token.span.clone()),
                        expression,
                    ),
                    span,
                )
            }
            TokenKind::True => {
                self.potential_tokens.clear();
                self.push_expression(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Boolean(true),
                        token.span.clone(),
                    )),
                    token.span.clone(),
                )
            }
            TokenKind::False => {
                self.potential_tokens.clear();
                self.push_expression(
                    ExpressionKind::Literal(Literal::new(
                        LiteralKind::Boolean(false),
                        token.span.clone(),
                    )),
                    token.span.clone(),
                )
            }
            TokenKind::OpenBracket => {
                self.potential_tokens.clear();
                self.parse_array_instantiation(token.span)
            }
            TokenKind::OpenParenthesis => {
                self.potential_tokens.clear();
                let open_loc = token.span;

                let expr_id = self.parse_expression(true, allow_assignment).0.id;
                let token = self.lexer.next_token();
                let span = if token.kind == TokenKind::CloseParenthesis {
                    &token.span
                } else {
                    report_missing_closing_token!(
                        self,
                        token,
                        TokenKind::CloseParenthesis,
                        TokenKind::OpenParenthesis,
                        open_loc
                    );
                    self.lexer.push_next(token);
                    &self.lexer.peek().span
                };

                // we need to alter the expression's span to account for open and close
                // parenthesis
                let expression = &mut self.compilation_unit.expressions[id!(expr_id)];
                expression.span = open_loc.extend_to(&expression.span).extend_to(span);
                expression.id
            }
            _ => {
                report_unexpected_token!(
                    self,
                    token,
                    [
                        expected_token!(TokenKind::If),
                        expected_token!(TokenKind::While),
                        expected_token!(TokenKind::Identifier),
                        expected_token!(TokenKind::Number(0)),
                        expected_token!(TokenKind::String("".to_string())),
                        expected_token!(TokenKind::Minus),
                        expected_token!(TokenKind::True),
                        expected_token!(TokenKind::False),
                        expected_token!(TokenKind::OpenBracket),
                        expected_token!(TokenKind::OpenParenthesis),
                    ]
                );
                // stuff that can legitimately come after an expression (or EOF because we need to
                // stop) - this probably means that the expression was actually missing.
                match &token.kind {
                    TokenKind::Eof
                    | TokenKind::Semicolon
                    | TokenKind::CloseBracket
                    | TokenKind::CloseParenthesis
                    | TokenKind::CloseCurlyBracket
                    | TokenKind::OpenParenthesis
                    | TokenKind::OpenCurlyBracket
                    | TokenKind::Dot
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
                            self.lexer.input_id(),
                            token.span.line,
                            token.span.column,
                            token.span.start,
                            0,
                        );
                        // let's keep parsing with the token that becomes legit thanks to the
                        // insertion of the dummy expression
                        self.lexer.push_next(token);
                        self.push_expression(ExpressionKind::Dummy, span)
                    }
                    _ => {
                        // try again after consuming the unexpected token
                        self.parse_expression_with_precedence(
                            precedence,
                            allow_struct,
                            allow_assignment,
                        )
                        .0
                        .id
                    }
                }
            }
        };

        // expr '...

        loop {
            match &self.lexer.peek().kind {
                TokenKind::Dot => {
                    // expr . 'identifier
                    let _dot = self.lexer.next_token();
                    self.potential_tokens.clear();

                    let token = self.lexer.next_token();
                    match &token.kind {
                        TokenKind::Identifier => {
                            self.potential_tokens.clear();
                            let identifier = Identifier::new(
                                self.push_identifier(&token.span),
                                token.span.clone(),
                            );
                            let identifier_ref = self.push_identifier_ref(identifier);

                            let span = self.compilation_unit.expressions[id!(expr_id)]
                                .span
                                .extend_to(&token.span);

                            expr_id = self.push_expression(
                                ExpressionKind::Access(expr_id, identifier_ref),
                                span,
                            );
                        }
                        _ => {
                            report_unexpected_token!(
                                self,
                                token,
                                [expected_token!(TokenKind::Identifier),]
                            );
                            // we ignore the dot and the non-identifier and keep parsing as if it did not exist
                        }
                    }
                }
                TokenKind::OpenBracket => {
                    // expr [ 'expression
                    let open_bracket = self.lexer.next_token();
                    self.potential_tokens.clear();

                    let index = self.parse_expression(true, false).0.id;

                    let close_bracket = self.lexer.next_token();

                    expr_id = self.push_expression(
                        ExpressionKind::ArrayAccess(expr_id, index),
                        open_bracket.span.extend_to(&close_bracket.span),
                    );

                    if !matches!(&close_bracket.kind, TokenKind::CloseBracket) {
                        report_missing_token_and_push_back!(
                            self,
                            close_bracket,
                            [
                                expected_token!(TokenKind::CloseBracket),
                                expected_token!(TokenKind::EqualEqual),
                                expected_token!(TokenKind::ExclaimEqual),
                                expected_token!(TokenKind::Greater),
                                expected_token!(TokenKind::GreaterEqual),
                                expected_token!(TokenKind::Smaller),
                                expected_token!(TokenKind::SmallerEqual),
                                expected_token!(TokenKind::Minus),
                                expected_token!(TokenKind::Plus),
                                expected_token!(TokenKind::Slash),
                                expected_token!(TokenKind::Star),
                                expected_token!(TokenKind::Dot),
                                expected_token!(TokenKind::OpenBracket),
                                expected_token!(TokenKind::OpenParenthesis),
                            ]
                        );
                    }
                }
                TokenKind::OpenParenthesis => {
                    expr_id = self.parse_function_call(expr_id).id;
                    allow_assignment = false;
                }
                _ => {
                    // ignore and keep parsing
                    self.potential_tokens
                        .insert(expected_token!(TokenKind::Dot));
                    self.potential_tokens
                        .insert(expected_token!(TokenKind::OpenBracket));
                    self.potential_tokens
                        .insert(expected_token!(TokenKind::OpenParenthesis));
                    break;
                }
            }
        }

        // x.y.z[a][b].a[1].b

        let mut need_semi = false;

        if allow_assignment {
            if self.lexer.peek().kind == TokenKind::Equal {
                // ... '= ...
                let lhs = self.compilation_unit.expressions.pop().unwrap();
                match &lhs.kind {
                    ExpressionKind::Literal(literal) => match &literal.kind {
                        LiteralKind::Identifier(ident_ref_id) => {
                            self.lexer.next_token();
                            self.potential_tokens.clear();
                            need_semi = true;
                            allow_assignment = false;

                            let rhs = self.parse_expression(allow_struct, allow_assignment).0;
                            let span = lhs.span.extend_to(&rhs.span);
                            let rhs_id = rhs.id;

                            expr_id = self.push_expression(
                                ExpressionKind::Assignment(Target::Direct(*ident_ref_id), rhs_id),
                                span,
                            );
                        }
                        _ => {
                            self.potential_tokens
                                .insert(expected_token!(TokenKind::Identifier));
                            self.compilation_unit.expressions.push(lhs);
                        }
                    },
                    ExpressionKind::Access(_, _) | ExpressionKind::ArrayAccess(_, _) => {
                        self.lexer.next_token();
                        self.potential_tokens.clear();
                        need_semi = true;

                        let lhs_id = lhs.id;
                        let lhs_span = lhs.span.clone();

                        self.compilation_unit.expressions.push(lhs);

                        let rhs = self.parse_expression(allow_struct, allow_assignment).0;
                        let span = lhs_span.extend_to(&rhs.span);
                        let rhs_id = rhs.id;

                        expr_id = self.push_expression(
                            ExpressionKind::Assignment(Target::Indirect(lhs_id), rhs_id),
                            span,
                        );
                    }
                    _ => {
                        self.compilation_unit.expressions.push(lhs);
                    }
                }
            } else {
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Equal));
            }
        }

        while let Some(operator) = self.parse_binary_operator_with_higher_precedence(precedence) {
            need_semi = true;
            expr_id = self
                .parse_infix_expression(expr_id, operator, allow_struct, allow_assignment)
                .id;
        }

        (&self.compilation_unit.expressions[id!(expr_id)], need_semi)
    }

    fn parse_array_instantiation(&mut self, start_span: Span) -> ExprId {
        // [ 'expr ... ]

        let (arguments, end_span) = self.parse_arguments(1, TokenKind::CloseBracket);

        let span = start_span.extend_to(&end_span);
        self.push_expression(ExpressionKind::ArrayInstantiation(arguments), span)
    }

    fn parse_binary_operator_with_higher_precedence(
        &mut self,
        precedence: Precedence,
    ) -> Option<BinaryOperator> {
        let token = self.lexer.next_token();

        match &token.kind {
            TokenKind::EqualEqual => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Equality,
                    token.span.clone(),
                ))
            }
            TokenKind::ExclaimEqual => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::NonEquality,
                    token.span.clone(),
                ))
            }
            TokenKind::Greater => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::GreaterThan,
                    token.span.clone(),
                ))
            }
            TokenKind::GreaterEqual => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::GreaterThanOrEqualTo,
                    token.span.clone(),
                ))
            }
            TokenKind::Smaller => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::SmallerThan,
                    token.span.clone(),
                ))
            }
            TokenKind::SmallerEqual => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::SmallerThanOrEqualTo,
                    token.span.clone(),
                ))
            }
            TokenKind::Minus => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Subtraction,
                    token.span.clone(),
                ))
            }
            TokenKind::Plus => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Addition,
                    token.span.clone(),
                ))
            }
            TokenKind::Slash => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Division,
                    token.span.clone(),
                ))
            }
            TokenKind::Star => {
                self.potential_tokens.clear();
                Some(BinaryOperator::new(
                    BinaryOperatorKind::Multiplication,
                    token.span.clone(),
                ))
            }
            _ => {
                self.potential_tokens
                    .insert(expected_token!(TokenKind::EqualEqual));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::ExclaimEqual));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Greater));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::GreaterEqual));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Smaller));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::SmallerEqual));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Minus));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Plus));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Slash));
                self.potential_tokens
                    .insert(expected_token!(TokenKind::Star));
                None
            }
        }
        .and_then(|op| {
            if op.kind.precedence() > precedence {
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

    fn parse_infix_expression(
        &mut self,
        left: ExprId,
        operator: BinaryOperator,
        allow_struct: bool,
        allow_assignment: bool,
    ) -> &Expression {
        let left_span = self.compilation_unit.expressions[id!(left)].span.clone();

        let right = self
            .parse_expression_with_precedence(
                operator.kind.precedence(),
                allow_struct,
                allow_assignment,
            )
            .0;

        let span = left_span.extend_to(&right.span);

        let id = right.id;
        let id = self.push_expression(ExpressionKind::Binary(left, operator, id), span);

        &self.compilation_unit.expressions[id!(id)]
    }

    /// Parses the following (the `if` keyword is already consumed):
    /// ```raw
    /// if expr { expr ; ... } else if expr { expr ; } else { expr ; ... }
    /// ```
    fn parse_if_expression(&mut self, span: Span) -> &Expression {
        let mut full_span = span;

        // if 'expr { expr ; ... } ...
        let condition = self.parse_expression(false, false).0.id;

        // if expr '{ expr ; ... } ...
        let open_curly_bracket = self.lexer.next_token();
        let open_curly_bracket_span = open_curly_bracket.span.clone();

        if open_curly_bracket.kind != TokenKind::OpenCurlyBracket {
            report_unexpected_token!(
                self,
                open_curly_bracket,
                [expected_token!(TokenKind::OpenCurlyBracket),]
            );
            self.lexer.push_next(open_curly_bracket);
        }
        self.potential_tokens.clear();

        let (true_statements, true_statements_span) =
            self.parse_statements(&open_curly_bracket_span);

        let true_expression_span = open_curly_bracket_span.extend_to(&true_statements_span);
        full_span = full_span.extend_to(&true_expression_span);

        let true_expr_id =
            self.push_expression(ExpressionKind::Block(true_statements), true_expression_span);

        // ... 'else if expr { expr ; ... } else { expr ; ... }
        let false_expr_id = if self.lexer.peek().kind == TokenKind::Else {
            let _else_token = self.lexer.next_token();
            let token = self.lexer.next_token();
            let false_block = match &token.kind {
                TokenKind::If => {
                    self.potential_tokens.clear();
                    // ... else 'if expr { expr ; ... } ...
                    let expression = self.parse_if_expression(token.span.clone());
                    let id = expression.id;
                    let span = expression.span.clone();
                    Some((
                        vec![self.push_statement(StatementKind::Expression(id), span.clone())],
                        span,
                    ))
                }
                // else '{ expr ; ... }
                TokenKind::OpenCurlyBracket => {
                    self.potential_tokens.clear();
                    let (statements, statements_span) = self.parse_statements(&token.span);
                    Some((statements, token.span.extend_to(&statements_span)))
                }
                _ => {
                    report_unexpected_token!(
                        self,
                        token,
                        [
                            expected_token!(TokenKind::If),
                            expected_token!(TokenKind::OpenCurlyBracket),
                        ]
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

        &self.compilation_unit.expressions[id!(id)]
    }

    fn parse_while_expression(&mut self, span: Span) -> &Expression {
        // while 'expr { expr ; ... }
        let condition = self.parse_expression(false, false).0.id;
        let open_curly_bracket = self.lexer.next_token();
        let open_curly_bracket_span = open_curly_bracket.span.clone();

        if open_curly_bracket.kind != TokenKind::OpenCurlyBracket {
            report_unexpected_token!(
                self,
                open_curly_bracket,
                [expected_token!(TokenKind::OpenCurlyBracket),]
            );
            self.lexer.push_next(open_curly_bracket);
        }
        self.potential_tokens.clear();

        let (statements, statements_span) = self.parse_statements(&open_curly_bracket_span);

        let block_span = open_curly_bracket_span.extend_to(&statements_span);

        let expr_id = self.push_expression(ExpressionKind::Block(statements), block_span);

        let id = self.push_expression(
            ExpressionKind::While(condition, expr_id),
            span.extend_to(&statements_span),
        );

        &self.compilation_unit.expressions[id!(id)]
    }

    /// Parses the following:
    /// ```raw
    /// identifier ( expr , ... )
    /// ```
    fn parse_function_call(&mut self, expr_id: ExprId) -> &Expression {
        // identifier '( expr , ... )
        self.potential_tokens.clear();
        let open_parenthesis_token = self.lexer.next_token();

        assert_eq!(&open_parenthesis_token.kind, &TokenKind::OpenParenthesis);

        let (arguments, span) = self.parse_arguments(0, TokenKind::CloseParenthesis);
        let span = self.compilation_unit.expressions[id!(expr_id)]
            .span
            .extend_to(&span);

        // identifier ( expr , ... ) '
        let id = self.push_expression(ExpressionKind::FunctionCall(expr_id, arguments), span);

        &self.compilation_unit.expressions[id!(id)]
    }

    fn parse_arguments(
        &mut self,
        min_arguments_count: usize,
        closing_token: TokenKind,
    ) -> (Vec<ExprId>, Span) {
        let mut arguments = Vec::new();
        let mut comma_seen = true;

        let span = loop {
            let token = self.lexer.next_token();
            if token.kind == closing_token {
                if arguments.len() < min_arguments_count {
                    if !comma_seen {
                        report_unexpected_token!(self, token, [expected_token!(TokenKind::Comma),]);
                    } else {
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(TokenKind::Identifier),
                                expected_token!(TokenKind::Number(0)),
                                expected_token!(TokenKind::Minus),
                                expected_token!(TokenKind::True),
                                expected_token!(TokenKind::False),
                                expected_token!(TokenKind::OpenBracket),
                                expected_token!(TokenKind::OpenParenthesis),
                                expected_token!(TokenKind::If),
                                expected_token!(TokenKind::While),
                            ]
                        );
                    }
                }
                self.potential_tokens.clear();
                break token.span;
            }

            match &token.kind {
                TokenKind::Comma => {
                    if !comma_seen {
                        self.potential_tokens.clear();
                        comma_seen = true;
                    } else {
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(closing_token.clone()),
                                expected_token!(TokenKind::Identifier),
                                expected_token!(TokenKind::Number(0)),
                                expected_token!(TokenKind::Minus),
                                expected_token!(TokenKind::True),
                                expected_token!(TokenKind::False),
                                expected_token!(TokenKind::OpenBracket),
                                expected_token!(TokenKind::OpenParenthesis),
                                expected_token!(TokenKind::If),
                                expected_token!(TokenKind::While),
                            ]
                        );
                    }
                }
                TokenKind::Eof | TokenKind::Semicolon => {
                    let span = token.span.clone();
                    if !comma_seen {
                        if arguments.len() < min_arguments_count {
                            report_unexpected_token!(
                                self,
                                token,
                                [expected_token!(TokenKind::Comma),]
                            );
                        } else {
                            report_unexpected_token!(
                                self,
                                token,
                                [
                                    expected_token!(TokenKind::Comma),
                                    expected_token!(closing_token.clone()),
                                ]
                            );
                        }
                    } else if arguments.len() < min_arguments_count {
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(TokenKind::Identifier),
                                expected_token!(TokenKind::Number(0)),
                                expected_token!(TokenKind::Minus),
                                expected_token!(TokenKind::True),
                                expected_token!(TokenKind::False),
                                expected_token!(TokenKind::OpenBracket),
                                expected_token!(TokenKind::OpenParenthesis),
                                expected_token!(TokenKind::If),
                                expected_token!(TokenKind::While),
                            ]
                        );
                    } else {
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(closing_token.clone()),
                                expected_token!(TokenKind::Identifier),
                                expected_token!(TokenKind::Number(0)),
                                expected_token!(TokenKind::Minus),
                                expected_token!(TokenKind::True),
                                expected_token!(TokenKind::False),
                                expected_token!(TokenKind::OpenBracket),
                                expected_token!(TokenKind::OpenParenthesis),
                                expected_token!(TokenKind::If),
                                expected_token!(TokenKind::While),
                            ]
                        );
                    }

                    self.lexer.push_next(token);
                    break span;
                }
                _ => {
                    if !comma_seen {
                        report_missing_token_and_push_back!(self, token, TokenKind::Comma);
                    } else {
                        self.lexer.push_next(token);
                    }

                    arguments.push(self.parse_expression(true, false).0.id);
                    comma_seen = false;
                }
            }
        };

        (arguments, span)
    }

    fn parse_struct_instantiation(
        &mut self,
        struct_identifier: Identifier,
        generic_types: Vec<TypeDefId>,
    ) -> ExprId {
        // ident '{ ident : expr , ... }
        let open_curly_bracket_token = self.lexer.next_token();
        self.potential_tokens.clear();

        assert_eq!(&open_curly_bracket_token.kind, &TokenKind::OpenCurlyBracket);

        // ident { 'ident : expr , ... }

        let mut fields = Vec::new();
        let mut expect_more = false;

        let last_token = loop {
            let token = self.lexer.next_token();
            match &token.kind {
                TokenKind::CloseCurlyBracket => {
                    self.potential_tokens.clear();
                    // ident { ... '}
                    break token;
                }
                TokenKind::Identifier => {
                    self.potential_tokens.clear();
                    // ident { ... , 'ident : expr , ... '}

                    let identifier =
                        Identifier::new(self.push_identifier(&token.span), token.span.clone());
                    let ident_ref_id = self.push_identifier_ref(identifier);
                    expect_more = false;

                    // ident { ... , ident ': expr , ... '}
                    let token = self.lexer.next_token();
                    match &token.kind {
                        TokenKind::Colon => {}
                        _ => {
                            // we miss the colon
                            report_unexpected_token!(
                                self,
                                token,
                                [expected_token!(TokenKind::Colon),]
                            );
                            // we may have consumed a comma. in order to avoid missing it, we push
                            // the token back
                            self.lexer.push_next(token);
                            self.take_until_one_of(vec![
                                // S { a ^b ': ...
                                TokenKind::Colon,
                                // S { a ^b ', ...
                                TokenKind::Comma,
                                // S { a ^b '}
                                TokenKind::CloseCurlyBracket,
                            ]);

                            let token = self.lexer.next_token();
                            match &token.kind {
                                TokenKind::Colon => {
                                    self.potential_tokens.clear();
                                    // we finally found a colon, we continue parsing the current
                                    // field from here, ignoring everything between the field name
                                    // and the colon we just found

                                    // ident { ... , ident ... ': ident , ... }
                                }
                                TokenKind::Comma => {
                                    self.potential_tokens.clear();
                                    // we found a comma, which means that the current
                                    // field was not completed. we can start over for the
                                    // next one

                                    // ident { ... , ident ... ', ... }
                                    expect_more = true;
                                    continue;
                                }
                                TokenKind::CloseCurlyBracket => {
                                    self.potential_tokens.clear();
                                    // we reached the end of the struct
                                    break token;
                                }
                                _ => unreachable!(),
                            }
                        }
                    }

                    // ident { ... , ident : 'expr , ... '}
                    let expr = self.parse_expression(true, false).0;

                    fields.push((ident_ref_id, expr.id));

                    // finally, if the next token is a comma, we eat it and continue
                    // processing the next field
                    let token = self.lexer.peek();
                    if token.kind == TokenKind::Comma {
                        self.lexer.next_token();
                        self.potential_tokens.clear();
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
                            [
                                expected_token!(TokenKind::CloseCurlyBracket),
                                expected_token!(TokenKind::Identifier),
                            ]
                        );
                    } else {
                        // we did not expect one mode field (we did not see a comma), which means
                        // the next token would either be a closing bracket or a comma
                        report_unexpected_token!(
                            self,
                            token,
                            [
                                expected_token!(TokenKind::CloseCurlyBracket),
                                expected_token!(TokenKind::Comma),
                            ]
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
                        [
                            expected_token!(TokenKind::CloseCurlyBracket),
                            expected_token!(TokenKind::Identifier),
                        ]
                    );

                    // and we skip tokens to sync
                    self.take_until_one_of(vec![TokenKind::Comma, TokenKind::CloseCurlyBracket]);
                    let token = self.lexer.peek();
                    if token.kind == TokenKind::Comma {
                        self.lexer.next_token();
                        expect_more = true
                    }
                }
            }
        };

        let span = struct_identifier.span.extend_to(&last_token.span);
        let struct_ident_ref_id = self.push_identifier_ref(struct_identifier);

        self.push_expression(
            ExpressionKind::StructInstantiation(struct_ident_ref_id, generic_types, fields),
            span,
        )
    }

    fn parse_semicolon(&mut self) -> Span {
        let token = self.lexer.peek();
        if token.kind == TokenKind::Semicolon {
            let span = self.lexer.next_token().span.clone();
            self.potential_tokens.clear();
            span
        } else {
            let token = self.lexer.next_token();
            report_unexpected_token!(self, token, [expected_token!(TokenKind::Semicolon),]);
            self.take_until_one_of(vec![TokenKind::Semicolon]);
            self.lexer.next_token().span.clone() // consume the semicolon, if it's there (otherwise, we have eof)
        }
    }

    /// the returned span includes the closing }
    fn parse_statements(&mut self, open_curly_bracket_span: &Span) -> (Vec<StmtId>, Span) {
        let mut statements = Vec::new();
        loop {
            let token = self.lexer.peek();
            match &token.kind {
                TokenKind::CloseCurlyBracket => {
                    break;
                }
                _ => {
                    self.potential_tokens
                        .insert(expected_token!(TokenKind::CloseCurlyBracket));
                    if let Some(statement) = self.parse_statement() {
                        statements.push(statement.id);
                    } else {
                        // we were not able to parse a statement, let's quit the loop
                        break;
                    }
                }
            }
        }

        let token = self.lexer.next_token();
        let span = token.span.clone();
        if token.kind != TokenKind::CloseCurlyBracket {
            report_missing_closing_token!(
                self,
                token,
                TokenKind::CloseCurlyBracket,
                TokenKind::OpenCurlyBracket,
                open_curly_bracket_span
            );
        } else {
            self.potential_tokens.clear();
        }

        // not the whole span, the last token's span, which is good enough as we only want to know
        // where the statements end
        (statements, span)
    }

    fn push_identifier(&mut self, span: &Span) -> IdentId {
        let ident = self.lexer.span(span);
        if let Some(id) = self.compilation_unit.identifiers.get_by_left(ident) {
            *id
        } else {
            let id = IdentId::from(self.compilation_unit.identifiers.len());
            self.compilation_unit
                .identifiers
                .insert(ident.to_string(), id);
            id
        }
    }

    fn push_identifier_ref(&mut self, ident: Identifier) -> IdentRefId {
        let id = self.compilation_unit.identifier_refs.create();
        self.compilation_unit
            .identifier_refs
            .insert(id, IdentifierRef::new(id, ident));
        id
    }

    fn push_expression(&mut self, kind: ExpressionKind, span: Span) -> ExprId {
        let id = ExprId::from(self.compilation_unit.expressions.len());
        self.compilation_unit
            .expressions
            .push(Expression::new(id, kind, span));
        id
    }

    fn push_statement(&mut self, kind: StatementKind, span: Span) -> StmtId {
        let id = self.compilation_unit.statements.create();
        self.compilation_unit
            .statements
            .insert(id, Statement::new(id, kind, span));
        id
    }

    /// Consumes tokens until one of supplied one is found. It does NOT consume it.
    /// Returns the amount of skipped tokens
    fn take_until_one_of(&mut self, mut token_kinds: Vec<TokenKind>) -> usize {
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
        while f(&token.kind) {
            self.lexer.next_token();
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
    use transmute_core::ids::InputId;

    macro_rules! test_syntax {
        ($name:ident => $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit: CompilationUnit = Default::default();
                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), $src),
                )
                .parse();
                assert_debug_snapshot!(compilation_unit.into_ast());
            }
        };
    }

    test_syntax!(expression_literal_number => "42;");
    test_syntax!(expression_literal_identifier => "forty_two;");
    test_syntax!(expression_literal_boolean => "true;");
    test_syntax!(expression => "2 + 20 * 2;");
    test_syntax!(expression_with_diagnostic_reported_by_lexer => "\"Hello\\gworld!\";");
    test_syntax!(binary_operator_minus => "43 - 1;");
    test_syntax!(prefix_minus => "- 40 * 2;");
    test_syntax!(let_statement => "let forty_two = 42;");
    test_syntax!(assignment => "forty_two = 42;");
    test_syntax!(access => "forty . two ;");
    test_syntax!(access_nested => "forty . two . something;");
    test_syntax!(access_equal => "forty . two = 1;");
    test_syntax!(access_precendence => "-a.b;");
    test_syntax!(err_access => "a.1;");
    test_syntax!(two_statements => "let forty_two = 42; forty_two;");
    test_syntax!(function_statement => "let times_two(a: number) = a * 2;");
    test_syntax!(function_statement_with_return_type => "let times_two(a: number): number = a * 2;");
    test_syntax!(function_statements => "let times_two(a: number) = { a * 2; }");
    test_syntax!(function_statements_without_equal => "let times_two(a: number) { a * 2; }");
    test_syntax!(function_call => "times_two(21);");
    test_syntax!(function_call_in_deep_nested_namespace => "ns1.ns2.times_two(21);");
    test_syntax!(ret => "ret 42;");
    test_syntax!(ret_void => "ret;");
    test_syntax!(ret_missing_next_token => "ret");
    test_syntax!(empty_statement => ";");
    test_syntax!(empty_statement_followed_by_non_empty => "; ret 42;");
    test_syntax!(function_empty_block => "let a() {}");
    test_syntax!(function_block_empty_statement => "let a() {;}");
    test_syntax!(if_simple => "if true { 42; }");
    test_syntax!(if_else => "if true { 42; } else { 43; }");
    test_syntax!(if_else_if_else => "if true { 42; } else if false { 43; } else { 44; }");
    test_syntax!(while_loop => "while true { 42; }");
    test_syntax!(struct_valid_zero_field => "struct S { }");
    test_syntax!(struct_valid_one_field => "struct S { a: number }");
    test_syntax!(struct_valid_several_fields => "struct S { a: number, b: number }");
    test_syntax!(struct_valid_trailing_comma => "struct S { a: number, }");
    test_syntax!(struct_valid_type_param => "struct S<T> { a: T }");
    test_syntax!(struct_valid_type_params => "struct S<T,U> { a: T }");
    test_syntax!(struct_valid_type_params_trailing_comma => "struct S<T,U,> { a: T }");
    test_syntax!(structs_as_root => "struct S { } struct S { }");
    test_syntax!(protected_struct_in_if_expression => "if (Struct {}) {}");
    test_syntax!(protected_struct_in_while_expression => "while (Struct {}) {}");
    test_syntax!(struct_instantiation_empty => "S { };");
    test_syntax!(struct_instantiation_one_field => "S { x: 1 };");
    test_syntax!(struct_instantiation_two_fields => "S { x: 1, y: 2 };");
    test_syntax!(struct_instantiation_two_fields_trailing_coma => "S { x: 1, y: 2, };");
    test_syntax!(struct_instantiation_generic => "S!<String> { s: \"string\" };");
    test_syntax!(struct_instantiation_generic2 => "S!<String, Integer> { s: \"string\" };");
    test_syntax!(struct_instantiation_generic3 => "S!<String, > { s: \"string\" };");
    test_syntax!(err_struct_instantiation_generic_missing_closing => "S!<String { s: \"string\" };");
    test_syntax!(err_struct_instantiation_generic_missing_commma => "S!<String Integer> { s: \"string\" };");
    test_syntax!(array_instantiation_one_element => "[0];");
    test_syntax!(array_instantiation_two_elements => "[0, 2];");
    test_syntax!(array_instantiation_trailing_comma => "[0, 2, ];");
    test_syntax!(err_expression_missing_right_parenthesis => "(42;");
    test_syntax!(err_expression_missing_right_parenthesis_eof => "(42");
    test_syntax!(err_expression_inserted_token_before_expression => "^42;");
    test_syntax!(err_expression_missing_token_at_eof => "1 + ");
    test_syntax!(err_expression_missing_token => "1 + ;");
    test_syntax!(err_let_missing_identifier => "let = 42;");
    test_syntax!(err_let_missing_equal => "let forty_two 42;");
    test_syntax!(err_let_missing_expression => "let forty_two = ;");
    test_syntax!(err_let_missing_semicolon_after_number => "let forty_two = 42");
    test_syntax!(err_let_missing_semicolon_after_ident => "let forty_two = a");
    test_syntax!(err_let_fn_params_unwanted_comma => "let x(,n:i,,m:j,) = { }");
    test_syntax!(err_let_fn_params_invalid_token_in_parameters_list => "let x(if) = { }");
    test_syntax!(err_let_fn_params_missing_colon_before_type => "let f(n integer) = { }");
    test_syntax!(err_let_fn_params_missing_type => "let f(n:) = { }");
    test_syntax!(err_let_fn_params_missing_colon_and_type => "let f(n) = { }");
    test_syntax!(err_let_fn_eof_in_params => "let x(");
    test_syntax!(err_let_fn_missing_equal => "let x() 1;");
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
    test_syntax!(err_function_call_missing_closing_parenthesis => "f(42;");
    test_syntax!(err_function_call_missing_closing_parenthesis_no_arguments => "f(;");
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
    test_syntax!(err_struct_missing_comma_in_type_parameters => "struct S <A B> { }");
    test_syntax!(err_struct_missing_identifier_in_type_parameters => "struct S <, B> { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters1 => "struct S <A { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters2 => "struct S <A, { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters3 => "struct S < { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters4 => "struct S <A 0 { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters5 => "struct S <A, 0 { }");
    test_syntax!(err_struct_missing_greater_after_type_parameters6 => "struct S < 0 { }");
    test_syntax!(err_struct_instantiation_missing_open_curly_one_field => "S a: a }");
    test_syntax!(err_struct_instantiation_missing_open_curly_no_fields => "S }");
    test_syntax!(err_struct_instantiation_missing_close_curly_one_field => "S { a: a");
    test_syntax!(err_struct_instantiation_missing_close_curly_one_field_trailing_comma => "S { a: a,");
    test_syntax!(err_struct_instantiation_missing_close_curly_no_fields => "S {");
    test_syntax!(err_struct_instantiation_missing_first_field_name => "S { : a, b: a, c: a };");
    test_syntax!(err_struct_instantiation_missing_second_field_name => "S { a: a, : a, c: a };");
    test_syntax!(err_struct_instantiation_missing_third_field_name => "S { a: a, b: a, : a };");
    test_syntax!(err_struct_instantiation_missing_first_field_colon => "S { a a, b: a, c: a };");
    test_syntax!(err_struct_instantiation_missing_second_field_colon => "S { a: a, b a, c: a };");
    test_syntax!(err_struct_instantiation_missing_third_field_colon => "S { a: a, b: a, c a };");
    test_syntax!(err_struct_instantiation_missing_first_field_value => "S { a: , b: a, c: a };");
    test_syntax!(err_struct_instantiation_missing_second_field_value => "S { a: a, b: , c: a };");
    test_syntax!(err_struct_instantiation_missing_third_field_value => "S { a: a, b: a, c: };");
    test_syntax!(err_struct_instantiation_missing_semicolon => "S { a: a }");
    test_syntax!(err_struct_wrong_equal => "struct S = { f1: number, f2: number }");
    test_syntax!(err_unprotected_struct_in_if_expression_1 => "if Point{} {}");
    test_syntax!(err_unprotected_struct_in_if_expression_2 => "if Point{} - 1 {}");
    test_syntax!(err_unprotected_struct_in_if_expression_3 => "if 1 - Point{} {}");
    test_syntax!(err_unprotected_struct_in_if_expression_4 => "if (1 + 1) - Point{} {}");
    test_syntax!(err_unprotected_struct_in_while_expression_1 => "while Point{} {}");
    test_syntax!(err_missing_semicolon_after_if_expression => "if true { 1; } else{ 1; } - 1 12;");
    test_syntax!(err_array_instantiation_empty => "[];");
    test_syntax!(err_array_instantiation_missing_element => "[0, ,];");
    test_syntax!(err_array_instantiation_missing_closing_bracket_no_element => "[;");
    test_syntax!(err_array_instantiation_missing_closing_bracket => "[0;");
    test_syntax!(err_array_instantiation_missing_closing_bracket_after_comma => "[0,;");
    test_syntax!(array_access => "a[0];");
    test_syntax!(array_access_multi => "a[0][0];");
    test_syntax!(array_access_expr => "a[i + 1];");
    test_syntax!(array_and_dot_access_1 => "a.b[0];");
    test_syntax!(array_and_dot_access_2 => "a[0].b;");
    test_syntax!(array_and_dot_access => "a.b[0].c;");
    test_syntax!(array_assign => "a[0] = 1;");
    test_syntax!(array_instantiation_and_access => "[1, 2][0];");
    test_syntax!(err_array_access_missing_bracked_semi => "a[0;");
    test_syntax!(err_array_access_missing_bracked_eof => "a[0");
    test_syntax!(array_type => "struct S { field: [number; 4] }");
    test_syntax!(array_type_nested => "struct S { field: [[number; 2]; 4] }");
    test_syntax!(err_array_type_missing_base => "struct S { field: [; 4] }");
    test_syntax!(err_array_type_missing_after_open_bracket => "struct S { field: [");
    test_syntax!(err_array_type_missing_semi => "struct S { field: [number 4] }");
    test_syntax!(err_array_type_missing_len => "struct S { field: [number; ] }");
    test_syntax!(err_array_type_missing_close_bracket => "struct S { field: [number; 4 }");
    test_syntax!(err_array_type_missing_after_base => "struct S { field: [number }");
    test_syntax!(annotation_on_fn => "@a let f() {}");
    test_syntax!(annotations_on_fn => "@a1 @a2 let f() {}");
    test_syntax!(annotation_on_struct => "@a struct S {}");
    test_syntax!(annotation_in_deep_namespace_on_fn => "@namespace1.namespace2.a struct S {}");
    test_syntax!(err_annotations_on_let => "let f() { @a1 @a2 let a = 1; }");
    test_syntax!(err_annotations_on_ret => "let f() { @a1 @a2 ret 1; }");
    test_syntax!(err_annotations_on_if => "let f() { @a1 if true {} }");
    test_syntax!(err_annotations_on_true => "let f() { @a1 while false {} }");
    test_syntax!(err_annotations_on_annotation => "@a1 annotation a2;");
    test_syntax!(err_annotations_without_identifier => "@ let f() { }");
    test_syntax!(define_annotation => "annotation a;");
    test_syntax!(err_define_annotation_with_at => "annotation @a;");
    test_syntax!(err_define_annotation_missing_name => "annotation ;");
    test_syntax!(err_define_annotation_missing_semi => "annotation a");
    test_syntax!(use_simple => "use a.b.c;");
    test_syntax!(define_namespace => "namespace ns;");
    test_syntax!(define_namespace_inline => "namespace ns {}");
    test_syntax!(define_namespace_inline_with_content => "namespace ns { let f() {} }");
    test_syntax!(define_namespace_inline_with_content_and_nested_function => r#"
        namespace root {
            let f() {}
            namespace ns1 {
                namespace ns2 {
                    let g() {}
                }
                let h() {
                    let i() {}
                }
            }
        }
    "#);
    test_syntax!(err_define_namespace_no_semi_no_open_curlybracket => "namespace ns invalid");
    test_syntax!(err_define_namespace_no_close_curlybracket => "namespace ns {");
    test_syntax!(nested_type => "let c(): ns1.ns2.type {}");
}
