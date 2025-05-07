use crate::expression::Expression;
use crate::identifier::Identifier;
use crate::identifier_ref::IdentifierRef;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::statement::{Statement, StatementKind, TypeDef};
use bimap::BiMap;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, IdentId, IdentRefId, InputId, StmtId, TypeDefId};
use transmute_core::input::{Input, Inputs};
use transmute_core::vec_map::VecMap;

pub mod annotation;
pub mod ast_print;
pub mod expression;
pub mod identifier;
pub mod identifier_ref;
pub mod lexer;
pub mod literal;
pub mod operators;
pub mod parser;
pub mod pretty_print;
pub mod statement;

pub fn parse(inputs: Vec<Input>) -> (Inputs, Result<Ast, Diagnostics<()>>) {
    let mut inputs = Inputs::from(inputs);
    let mut compilation_unit = CompilationUnit::default();

    for (input_id, input) in inputs.iter() {
        #[cfg(debug_assertions)]
        match input {
            Input::Core => println!("Parse core"),
            Input::File(path, _) => println!("Parse file      {}", path.display()),
            Input::Internal(name, _) => println!("Parse internal  {name}"),
        }
        Parser::new(
            &mut compilation_unit,
            None,
            Lexer::new(input_id, input.source()),
        )
        .parse();
    }

    while let Some(namespace_id) = compilation_unit.next_namespace() {
        let (name, input_id, _) = compilation_unit.statements[namespace_id].as_namespace();
        let file_name = format!(
            "{}.tm",
            compilation_unit.identifiers.get_by_right(&name.id).unwrap()
        );
        let path = match &inputs[input_id] {
            Input::Core => unreachable!(),
            Input::File(path_buf, _) => path_buf.with_extension("").join(file_name),
            Input::Internal(input_name, _) => unimplemented!(
                "internal input {input_name} cannot have namespaces ({name})",
                name = compilation_unit.identifiers.get_by_right(&name.id).unwrap()
            ),
        };

        println!("Parse file      {}", path.display());

        let input_id = inputs.push(Input::try_from(path).unwrap());

        Parser::new(
            &mut compilation_unit,
            Some(namespace_id),
            Lexer::new(input_id, inputs[input_id].source()),
        )
        .parse();
    }

    (inputs, compilation_unit.into_ast())
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
    /// Root statement
    pub root: StmtId,
}

impl Ast {
    pub fn new(
        identifiers: Vec<String>,
        identifier_refs: VecMap<IdentRefId, IdentifierRef>,
        expressions: Vec<Expression>,
        statements: VecMap<StmtId, Statement>,
        root: StmtId,
        type_defs: VecMap<TypeDefId, TypeDef>,
    ) -> Self {
        Self {
            identifiers: identifiers.into(),
            identifier_refs,
            expressions: expressions.into(),
            statements,
            type_defs,
            root,
        }
    }
}

pub struct CompilationUnit {
    identifiers: BiMap<String, IdentId>,
    identifier_refs: VecMap<IdentRefId, IdentifierRef>,
    expressions: Vec<Expression>,
    statements: VecMap<StmtId, Statement>,
    type_defs: VecMap<TypeDefId, TypeDef>,
    root: StmtId,
    diagnostics: Diagnostics<()>,

    namespaces: Vec<StmtId>,
}

impl Default for CompilationUnit {
    fn default() -> Self {
        let mut identifiers = BiMap::new();

        let root_ident_id = IdentId::from(identifiers.len());
        identifiers.insert("<root>".to_string(), root_ident_id);
        debug_assert_eq!(root_ident_id, IdentId::from(0));

        let mut statements = VecMap::new();
        let root_namespace = StmtId::from(statements.len());
        debug_assert_eq!(root_namespace, StmtId::from(0));

        statements.insert(
            root_namespace,
            Statement {
                id: root_namespace,
                kind: StatementKind::Namespace(
                    Identifier {
                        id: root_ident_id,
                        span: Default::default(),
                    },
                    InputId::from(0),
                    Vec::new(),
                ),
                span: Default::default(),
            },
        );

        Self {
            identifiers,
            identifier_refs: Default::default(),
            expressions: vec![],
            statements,
            type_defs: Default::default(),
            root: root_namespace,
            diagnostics: Default::default(),
            namespaces: vec![],
        }
    }
}

impl CompilationUnit {
    /// Returns the root namespace. The root namespace is a synthetic one.
    fn root_namespace(&self) -> StmtId {
        // the root namespace is StmtId, as per debug_assert in default() implementation
        StmtId::from(0)
    }

    /// Returns the next namespace to parse
    fn next_namespace(&mut self) -> Option<StmtId> {
        self.namespaces.pop()
    }

    pub fn into_ast(self) -> Result<Ast, Diagnostics<()>> {
        let mut identifiers = self
            .identifiers
            .into_iter()
            .collect::<Vec<(String, IdentId)>>();

        identifiers.sort_by(|(_, id1), (_, id2)| id1.cmp(id2));

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
                self.root,
                self.type_defs,
            ))
        } else {
            Err(self.diagnostics)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_debug_snapshot;
    use std::path::PathBuf;

    #[test]
    fn namespace() {
        let mut path_buf = PathBuf::from("test-resources");
        path_buf.push("root.tm");
        let (_, ast) = parse(vec![Input::try_from(path_buf).unwrap()]);
        assert_debug_snapshot!(ast.unwrap())
    }
}
