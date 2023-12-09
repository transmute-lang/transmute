use crate::ast::expression::ExpressionKind;
use crate::ast::ids::{make_id, ExprId, IdentId, StmtId};
use crate::ast::literal::{Literal, LiteralKind};
use crate::ast::statement::StatementKind;
use crate::ast::{Ast, Visitor};
use crate::symbol_table::{SymbolKind, SymbolTable};
use std::borrow::Cow;
use std::collections::HashMap;
use std::io;
use std::io::Write;

make_id!(NodeId);
make_id!(EdgeId);

#[derive(Clone)]
enum Node {
    // Identifier
    NativeIdentifier(IdentId),
    Identifier(IdentId),

    // Statements
    Let(IdentId),
    Ret,
    LetFn(IdentId, Vec<(IdentId, IdentId)>, Option<IdentId>),

    // Expressions
    Assignment,
    If,
    NativeFunctionCall(IdentId),
    FunctionCall(IdentId),
    While,

    // Literal
    Boolean(bool),
    Number(i64),

    // Other
    List,
    Empty,
    Text(String),
}

struct Edge {
    from: NodeId,
    to: NodeId,
    record_label: Option<String>,
    kind: EdgeKind,
}

#[derive(Default)]
enum EdgeKind {
    #[default]
    Default,
    TrueBranch,
    FalseBranch,
    Reference,
}

struct DotBuilder<'a> {
    ast: &'a Ast,
    symbols: &'a SymbolTable,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
    stmt_map: HashMap<StmtId, NodeId>,
    references: Vec<(NodeId, StmtId)>,
    parameter_references: Vec<(NodeId, StmtId, usize)>,
}

impl<'a> DotBuilder<'a> {
    pub fn new(ast: &'a Ast, symbols: &'a SymbolTable) -> Self {
        Self {
            ast,
            symbols,
            nodes: Default::default(),
            edges: Default::default(),
            stmt_map: Default::default(),
            references: Default::default(),
            parameter_references: Default::default(),
        }
    }

    pub fn build(mut self) -> Dot<'a> {
        self.ast.statements().iter().for_each(|s| {
            let node = self.visit_statement(*s);
            self.stmt_map.insert(*s, node);
        });

        self.references.iter().for_each(|(from, stmt)| {
            let to = self
                .stmt_map
                .get(stmt)
                .unwrap_or_else(|| panic!("Statement {stmt} not mapped"));

            if matches!(
                self.ast.statement(*stmt).kind(),
                StatementKind::LetFn(_, _, _, _)
            ) {
                self.edges.push(Edge {
                    from: *from,
                    to: *to,
                    record_label: Some("fn".to_string()),
                    kind: EdgeKind::Reference,
                });
            } else {
                self.edges.push(Edge {
                    from: *from,
                    to: *to,
                    record_label: None,
                    kind: EdgeKind::Reference,
                });
            }
        });
        self.parameter_references
            .iter()
            .for_each(|(from, stmt, index)| {
                let to = self
                    .stmt_map
                    .get(stmt)
                    .unwrap_or_else(|| panic!("Statement {stmt} not mapped"));
                self.edges.push(Edge {
                    from: *from,
                    to: *to,
                    record_label: Some(format!("p{index}")),
                    kind: EdgeKind::Reference,
                });
            });

        Dot {
            ast: self.ast,
            nodes: self.nodes,
            edges: self.edges,
        }
    }

    fn insert_node(&mut self, node: Node) -> NodeId {
        self.nodes.push(node);
        (self.nodes.len() - 1).into()
    }

    fn insert_edge(&mut self, from: NodeId, to: NodeId) -> EdgeId {
        self.edges.push(Edge {
            from,
            to,
            record_label: None,
            kind: Default::default(),
        });
        (self.edges.len() - 1).into()
    }

    fn insert_edge_with_kind(&mut self, from: NodeId, to: NodeId, kind: EdgeKind) -> EdgeId {
        self.edges.push(Edge {
            from,
            to,
            record_label: None,
            kind,
        });
        (self.edges.len() - 1).into()
    }
}

impl<'a> Visitor<NodeId> for DotBuilder<'a> {
    fn visit_statement(&mut self, stmt: StmtId) -> NodeId {
        let node_id = match self.ast.statement(stmt).kind() {
            StatementKind::Expression(expr) => self.visit_expression(*expr),
            StatementKind::Let(ident, expr) => {
                let expr_node_id = self.visit_expression(*expr);
                let let_node_id = self.insert_node(Node::Let(ident.id()));

                self.insert_edge(let_node_id, expr_node_id);

                let_node_id
            }
            StatementKind::Ret(expr) => {
                let expr_node_id = self.visit_expression(*expr);
                let ret_node_id = self.insert_node(Node::Ret);

                self.insert_edge(ret_node_id, expr_node_id);

                ret_node_id
            }
            StatementKind::LetFn(ident, params, ret, expr) => {
                let expr_node_id = self.visit_expression(*expr);
                let let_fn_node_id = self.insert_node(Node::LetFn(
                    ident.id(),
                    params
                        .iter()
                        .map(|p| (p.identifier().id(), p.ty().id()))
                        .collect::<Vec<(IdentId, IdentId)>>(),
                    ret.as_ref().map(|r| r.id()),
                ));
                self.insert_edge(let_fn_node_id, expr_node_id);

                let_fn_node_id
            }
        };

        self.stmt_map.insert(stmt, node_id);
        node_id
    }

    fn visit_expression(&mut self, expr: ExprId) -> NodeId {
        match self.ast.expression(expr).kind() {
            ExpressionKind::Assignment(ident_ref, expr) => {
                let ident = self.ast.identifier_ref(*ident_ref);
                let ident_node_id = self.insert_node(Node::Identifier(ident.ident().id()));
                let expr_node_id = self.visit_expression(*expr);
                let assignment_mode_id = self.insert_node(Node::Assignment);

                self.insert_edge(assignment_mode_id, ident_node_id);
                self.insert_edge(assignment_mode_id, expr_node_id);

                if let Some(symbol) = ident.symbol_id() {
                    match self.symbols.symbol(symbol).kind() {
                        SymbolKind::LetStatement(stmt) | SymbolKind::LetFnStatement(stmt, _) => {
                            self.references.push((ident_node_id, *stmt));
                        }
                        _ => panic!(),
                    }
                }

                assignment_mode_id
            }
            ExpressionKind::If(cond, true_branch, false_branch) => {
                let cond_node_id = self.visit_expression(*cond);
                let true_node_id = self.visit_expression(*true_branch);
                let false_node_id = false_branch.as_ref().map(|e| self.visit_expression(*e));
                let if_node_id = self.insert_node(Node::If);

                self.insert_edge(if_node_id, cond_node_id);
                self.insert_edge_with_kind(if_node_id, true_node_id, EdgeKind::TrueBranch);
                if let Some(false_node_id) = false_node_id {
                    self.insert_edge_with_kind(if_node_id, false_node_id, EdgeKind::FalseBranch);
                }

                if_node_id
            }
            ExpressionKind::Literal(lit) => match lit.kind() {
                LiteralKind::Boolean(b) => self.insert_node(Node::Boolean(*b)),
                LiteralKind::Identifier(ident) => {
                    let ident = self.ast.identifier_ref(*ident);

                    if let Some(symbol) = ident.symbol_id() {
                        match self.symbols.symbol(symbol).kind() {
                            SymbolKind::LetStatement(stmt)
                            | SymbolKind::LetFnStatement(stmt, _) => {
                                let ident_node_id =
                                    self.insert_node(Node::Identifier(ident.ident().id()));
                                self.references.push((ident_node_id, *stmt));
                                ident_node_id
                            }
                            SymbolKind::Parameter(_, stmt, index) => {
                                match self.ast.statement(*stmt).kind() {
                                    StatementKind::LetFn(_, params, _, _) => {
                                        let ident_node_id = self.insert_node(Node::Identifier(
                                            params.get(*index).unwrap().identifier().id(),
                                        ));
                                        self.parameter_references.push((
                                            ident_node_id,
                                            *stmt,
                                            *index,
                                        ));
                                        ident_node_id
                                    }
                                    _ => panic!(),
                                }
                            }
                            SymbolKind::Native(native) => self.insert_node(Node::NativeIdentifier(
                                self.ast.identifier_id(native.name()),
                            )),
                        }
                    } else {
                        self.insert_node(Node::Identifier(ident.ident().id()))
                    }
                }
                LiteralKind::Number(n) => self.insert_node(Node::Number(*n)),
            },
            ExpressionKind::Binary(left, op, right) => {
                let left_node_id = self.visit_expression(*left);
                let right_node_id = self.visit_expression(*right);
                let op_node_id = self.insert_node(Node::Text(op.kind().to_string()));

                self.insert_edge(op_node_id, left_node_id);
                self.insert_edge(op_node_id, right_node_id);

                op_node_id
            }
            ExpressionKind::FunctionCall(ident, params) => {
                let ident = self.ast.identifier_ref(*ident);

                let call_node_id = if let Some(symbol) = ident.symbol_id() {
                    match self.symbols.symbol(symbol).kind() {
                        SymbolKind::LetFnStatement(stmt, _) => {
                            let call_node_id =
                                self.insert_node(Node::FunctionCall(ident.ident().id()));
                            self.references.push((call_node_id, *stmt));
                            call_node_id
                        }
                        SymbolKind::Parameter(_, stmt, index) => {
                            match self.ast.statement(*stmt).kind() {
                                StatementKind::LetFn(_, params, _, _) => {
                                    let ident_node_id = self.insert_node(Node::FunctionCall(
                                        params.get(*index).unwrap().identifier().id(),
                                    ));
                                    self.parameter_references
                                        .push((ident_node_id, *stmt, *index));
                                    ident_node_id
                                }
                                _ => panic!(),
                            }
                        }
                        SymbolKind::Native(native) => self.insert_node(Node::NativeFunctionCall(
                            self.ast.identifier_id(native.name()),
                        )),
                        _ => panic!(),
                    }
                } else {
                    self.insert_node(Node::FunctionCall(ident.ident().id()))
                };

                params.iter().for_each(|e| {
                    let expr_node_id = self.visit_expression(*e);
                    self.insert_edge(call_node_id, expr_node_id);
                });

                call_node_id
            }
            ExpressionKind::Unary(op, expr) => {
                let expr_node_id = self.visit_expression(*expr);
                let op_node_id = self.insert_node(Node::Text(op.kind().to_string()));

                self.insert_edge(op_node_id, expr_node_id);

                op_node_id
            }
            ExpressionKind::While(cond, expr) => {
                let cond_node_id = self.visit_expression(*cond);
                let expr_node_id = self.visit_expression(*expr);
                let while_node_id = self.insert_node(Node::While);

                self.insert_edge(while_node_id, cond_node_id);
                self.insert_edge(while_node_id, expr_node_id);

                while_node_id
            }
            ExpressionKind::Block(stmts) => {
                if stmts.len() > 1 {
                    let list_node_id = self.insert_node(Node::List);

                    stmts.iter().for_each(|s| {
                        let node_id = self.visit_statement(*s);
                        self.insert_edge(list_node_id, node_id);
                    });

                    list_node_id
                } else {
                    self.visit_statement(*stmts.first().unwrap())
                }
            }
            ExpressionKind::Dummy => {
                unimplemented!()
            }
        }
    }

    fn visit_literal(&mut self, _literal: &Literal) -> NodeId {
        unimplemented!()
    }
}

pub struct Dot<'a> {
    ast: &'a Ast,
    nodes: Vec<Node>,
    edges: Vec<Edge>,
}

impl<'a> Dot<'a> {
    pub fn new(ast: &'a Ast, symbols: &'a SymbolTable) -> Self {
        DotBuilder::new(ast, symbols).build()
    }

    pub fn write<W: Write>(self, w: &mut W) -> io::Result<()> {
        w.write_all(self.serialize().as_bytes())
    }

    pub fn serialize(&self) -> String {
        let nodes = self
            .nodes
            .iter()
            .enumerate()
            .map(|(i, n)| self.serialize_node(i, n))
            .collect::<Vec<String>>()
            .join("\n");

        let edges = self
            .edges
            .iter()
            .map(|e| self.serialize_edge(e))
            .collect::<Vec<String>>()
            .join("\n");

        format!("digraph ast {{\nordering=\"out\";\nsplines=false;\n{nodes}\n{edges}}}")
    }

    fn serialize_node(&self, index: usize, node: &Node) -> String {
        let label = self.node_label(node);
        let shape = Self::node_shape(node);
        let font_color = Self::node_font_color(node);

        format!("n{index}[label=\"{label}\"][shape=\"{shape}\"][fontcolor=\"{font_color}\"]")
    }

    fn node_label(&self, node: &Node) -> Cow<str> {
        match node {
            Node::NativeIdentifier(ident) => Cow::Borrowed(self.ast.identifier(*ident)),
            Node::Identifier(ident) => Cow::Borrowed(self.ast.identifier(*ident)),
            Node::Let(ident) => Cow::Owned(format!("let {}", self.ast.identifier(*ident))),
            Node::Ret => Cow::Borrowed("ret"),
            Node::LetFn(ident, params, ret) => Cow::Owned(format!(
                "{{ {{<fn>let {}(){} }} | {{ {} }} }}",
                self.ast.identifier(*ident),
                ret.map(|r| format!(": {}", self.ast.identifier(r)))
                    .unwrap_or_default(),
                params
                    .iter()
                    .enumerate()
                    .map(|(i, (p, t))| format!(
                        "<p{i}>{}: {}",
                        self.ast.identifier(*p),
                        self.ast.identifier(*t)
                    ))
                    .collect::<Vec<String>>()
                    .join(" | "),
            )),
            Node::Assignment => Cow::Borrowed("set"),
            Node::If => Cow::Borrowed("if"),
            Node::NativeFunctionCall(ident) => {
                Cow::Owned(format!("{}()", self.ast.identifier(*ident)))
            }
            Node::FunctionCall(ident) => Cow::Owned(format!("{}()", self.ast.identifier(*ident))),
            Node::While => Cow::Borrowed("while"),
            Node::Boolean(val) => Cow::Owned(format!("{val}")),
            Node::Number(val) => Cow::Owned(format!("{val}")),
            Node::List => Cow::Borrowed(""),
            Node::Empty => Cow::Borrowed(""),
            Node::Text(val) => Cow::Owned(val.to_string()),
        }
    }

    fn node_shape(node: &Node) -> &'static str {
        match node {
            Node::List | Node::Empty => "point",
            Node::LetFn(_, _, _) => "record",
            _ => "plaintext",
        }
    }

    fn node_font_color(node: &Node) -> &'static str {
        match node {
            Node::NativeIdentifier(_) | Node::NativeFunctionCall(_) => "orange",
            Node::Identifier(_) | Node::FunctionCall(_) => "blue",
            _ => "black",
        }
    }

    fn serialize_edge(&self, edge: &Edge) -> String {
        let style = Self::edge_style(edge);
        let color = Self::edge_color(edge);
        let arrow_head = Self::edge_arrow_head(edge);
        let constraint = Self::edge_no_constraint(edge)
            .then_some("[constraint=false]")
            .unwrap_or_default();

        format!(
            "n{} -> n{}{}[style=\"{style}\"][color=\"{color}\"][arrowhead=\"{arrow_head}\"]{constraint}",
            edge.from, edge.to, edge.record_label.as_ref().map(|l| format!(":{l}")).unwrap_or_default()
        )
    }

    fn edge_style(edge: &Edge) -> &'static str {
        match edge.kind {
            EdgeKind::Reference => "dotted",
            _ => "solid",
        }
    }

    fn edge_color(edge: &Edge) -> &'static str {
        match edge.kind {
            EdgeKind::Reference => "gray",
            EdgeKind::TrueBranch => "green",
            EdgeKind::FalseBranch => "red",
            _ => "black",
        }
    }

    fn edge_arrow_head(edge: &Edge) -> &'static str {
        match edge.kind {
            EdgeKind::Reference => "vee",
            _ => "none",
        }
    }

    fn edge_no_constraint(edge: &Edge) -> bool {
        matches!(edge.kind, EdgeKind::Reference)
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Ast;
    use crate::dot::Dot;
    use crate::lexer::Lexer;
    use crate::natives::Natives;
    use crate::parser::Parser;
    use crate::symbol_table::SymbolTableGen;
    use crate::type_check::TypeChecker;
    use insta::assert_snapshot;

    macro_rules! generate {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let (ast, symbols) = {
                    let (ast, diagnostics) = Parser::new(Lexer::new($src)).parse();
                    assert!(diagnostics.is_empty(), "{:?}", diagnostics);

                    let natives = Natives::default();
                    let mut ast = ast.merge(Into::<Ast>::into(&natives));

                    let symbols = SymbolTableGen::new(&mut ast, natives).build_table();

                    let (ast, diagnostics) = TypeChecker::new(ast, &symbols).check();
                    assert!(diagnostics.is_empty(), "{:?}", diagnostics);

                    (ast, symbols)
                };

                assert_snapshot!(Dot::new(&ast, &symbols).serialize());
            }
        };
    }

    generate!(fibonacci_rec, "let fibo(n: number, m: number): number = { if n <= 1 { ret n; } else { fibo(n - 1) + fibo(n - 2); } }");
    generate!(
        fibonacci_iter,
        r#"
            let fibo(n: number): number = {
                if n == 0 { ret 0; }
                if n == 1 { ret 1; }

                let n = n;
                let prev_prev = 0;
                let prev = 1;
                let current = 0;

                while n > 1 {
                    current = prev_prev + prev;
                    prev_prev = prev;
                    prev = current;
                    n = n - 1;
                }

                current;
            }
        "#
    );
}
