use std::borrow::Cow;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter, Write};
use std::{fmt, mem};
use transmute_codegen::mangling::{mangle_function_name, mangle_struct_name};
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, StmtId, SymbolId, TypeId};
use transmute_mir::{
    Expression as MirExpression, ExpressionKind, LiteralKind, Mir, StatementKind, SymbolKind,
    Target as MirTarget, Type as MirType,
};
use transmute_mir::{Literal, NativeFnKind};

pub struct CCodegen<'mir> {
    mir: &'mir Mir,
    mangled_names: HashMap<SymbolId, Cow<'mir, str>>,
    types: HashMap<TypeId, Type>,
    structs: HashMap<SymbolId, Struct>,
    functions: HashMap<SymbolId, Function>,
}

#[derive(Debug)]
enum Type {
    Value(&'static str),
    SymbolPointer(SymbolId),
    Array(TypeId),
}

impl Type {
    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        match self {
            Type::Value(str) => format!("{str} ").into(),
            Type::SymbolPointer(sid) => format!("{} *", codegen.symbol_name(sid)).into(),
            Type::Array(tid) => format!("{}*", codegen.types[tid].gen_c(codegen),).into(),
        }
    }
}

#[derive(Debug)]
struct Function {
    /// The symbol holding the function's name (from CCodegen.mangled_names)
    symbol: SymbolId,
    return_type: TypeId,
    /// The function parameters
    parameters: Vec<SymbolId>,
    /// The variables declared in the function
    variables: Vec<SymbolId>,
    /// The expressions that we need to store in temp. variables
    expressions: Vec<ExprId>,
    /// The function blocks (in C term: delimited by `{` and `}`)
    block: Option<Block>,
    /// Generate the parent parameter?
    // todo: refactoring same as block.is_some()?
    gen_parent_parameter: bool,
}

impl Function {
    fn gen_declaration(&self, codegen: &CCodegen) -> CCode {
        let parameters = self
            .parameters
            .iter()
            .map(|sid| {
                format!(
                    include_str!("tmpl/function-parameter.txt"),
                    type = codegen.symbol_type_c(sid),
                    name = codegen.symbol_name(sid),
                )
            })
            .fold(String::new(), |mut acc, e| {
                if !acc.is_empty() || self.gen_parent_parameter {
                    acc.push_str(", ");
                }
                acc.push_str(e.as_str());
                acc
            });

        if self.gen_parent_parameter {
            format!(
                include_str!("tmpl/function-declaration.txt"),
                type = codegen.type_c(&self.return_type),
                name = codegen.symbol_name(&self.symbol),
                parameters = parameters,
            )
            .into()
        } else if self.parameters.is_empty() {
            format!(
                include_str!("tmpl/function-declaration-noframe-noparameters.txt"),
                type = codegen.type_c(&self.return_type),
                name = codegen.symbol_name(&self.symbol),
            )
            .into()
        } else {
            format!(
                include_str!("tmpl/function-declaration-noframe.txt"),
                type = codegen.type_c(&self.return_type),
                name = codegen.symbol_name(&self.symbol),
                parameters = parameters,
            )
            .into()
        }
    }

    fn gen_definition(&self, codegen: &CCodegen) -> Option<CCode> {
        self.block.as_ref().map(|block| {
            let body = CCode::from(
                block
                    .statements
                    .iter()
                    .map(|statement| statement.gen_c(codegen))
                    .fold(String::new(), |mut acc, e| {
                        acc.push_str(e.as_str());
                        acc
                    }),
            )
            .indent();

            if self.must_generate_frame() {
                format!(
                    include_str!("tmpl/function-definition.txt"),
                    declaration = self
                        .gen_declaration(codegen)
                        .as_str()
                        .trim()
                        .strip_suffix(";")
                        .unwrap(),
                    name = codegen.symbol_name(&self.symbol),
                    body = body.as_str().trim_end()
                )
            } else {
                format!(
                    include_str!("tmpl/function-definition-noframe.txt"),
                    declaration = self
                        .gen_declaration(codegen)
                        .as_str()
                        .trim()
                        .strip_suffix(";")
                        .unwrap(),
                    body = body.as_str().trim_end()
                )
            }
            .into()
        })
    }

    fn gen_frame(&self, codegen: &CCodegen) -> Option<CCode> {
        if !self.must_generate_frame() {
            return None;
        }

        // todo: arrays are not correctly represented: we have no info on size
        // todo: structs have no information on actual type
        // todo: non pointers are considered pointers (see e8 in array_access_expr test)

        let mut fields = Vec::with_capacity(self.variables.len() + self.expressions.len());
        for sid in self.variables.iter() {
            fields.push(format!(
                include_str!("tmpl/function-frame-field-var.txt"),
                type = codegen.symbol_type_c(sid),
                name = codegen.symbol_name(sid),
            ));
        }
        for eid in self.expressions.iter() {
            fields.push(format!(
                include_str!("tmpl/function-frame-field-expr.txt"),
                type = codegen.expression_type_c(eid),
                expr_id = eid
            ));
        }

        if fields.is_empty() {
            Some(
                format!(
                    include_str!("tmpl/function-frame-nofields.txt"),
                    fn_name = codegen.symbol_name(&self.symbol),
                )
                .into(),
            )
        } else {
            let fields = fields.into_iter().fold(String::new(), |mut acc, e| {
                acc.push_str(e.as_str());
                acc
            });

            Some(
                format!(
                    include_str!("tmpl/function-frame.txt"),
                    // +1 because the last element if the array is a NULL ptr
                    ptr_count = self.variables.len() + self.expressions.len() + 1,
                    fields = fields.trim_end(),
                    fn_name = codegen.symbol_name(&self.symbol),
                )
                .into(),
            )
        }
    }

    fn must_generate_frame(&self) -> bool {
        // !(self.variables.is_empty() && self.expressions.is_empty())
        self.block.is_some()
    }
}

#[derive(Debug)]
struct Block {
    statements: Vec<Statement>,
}

impl Block {
    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        let ccode = CCode::from(
            self.statements
                .iter()
                .map(|statement| statement.gen_c(codegen))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                }),
        )
        .indent();
        format!("{{\n{}\n}}", ccode.as_str().trim_end()).into()
    }
}

#[derive(Debug)]
enum Statement {
    Expression(Expression),
    Return(Vec<Statement>, Option<Value>),
}

impl Statement {
    #[cfg(debug_assertions)]
    fn has_prelude(&self) -> bool {
        match self {
            Statement::Expression(e) => e.has_prelude(),
            Statement::Return(prelude, ..) => !prelude.is_empty(),
        }
    }

    fn take_prelude(&mut self) -> Vec<Statement> {
        match self {
            Statement::Return(prelude, _) => mem::take(prelude),
            Statement::Expression(expression) => expression.take_prelude(),
        }
    }

    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        match self {
            Statement::Expression(expression) => {
                if expression.need_semi() {
                    format!(
                        include_str!("tmpl/statement-expression.txt"),
                        expression = expression.gen_c(codegen),
                    )
                    .into()
                } else {
                    format!(
                        include_str!("tmpl/statement-expression-nosemi.txt"),
                        expression = expression.gen_c(codegen),
                    )
                    .into()
                }
            }
            Statement::Return(prelude, Some(value)) => {
                let mut prelude = codegen.gen_c(prelude).0;
                prelude.push_str(
                    format!(
                        include_str!("tmpl/statement-return.txt"),
                        value = value.gen_c(codegen)
                    )
                    .as_str(),
                );
                prelude.into()
            }
            Statement::Return(prelude, None) => {
                let mut prelude = codegen.gen_c(prelude).0;
                prelude.push_str(include_str!("tmpl/statement-return-void.txt"));
                prelude.into()
            }
        }
    }
}

#[derive(Debug)]
enum Target {
    // todo: names (after merge of statement)
    Expression(ExprId),
    Exp(Box<Expression>),
    Symbol(SymbolId),
}

impl Target {
    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        match self {
            Target::Expression(eid) => format!("me.e{eid}").into(),
            Target::Exp(expression) => expression.gen_c(codegen),
            Target::Symbol(sid) => format!("me.{}", codegen.symbol_name(sid)).into(),
        }
    }
}

#[derive(Debug)]
struct Transformed<T: Debug> {
    element: T,
    variables: Vec<ExprId>,
}

#[derive(Debug)]
enum Expression {
    Intrinsic(
        /// the intrinsic
        Intrinsic,
    ),
    // todo: does not make a lot of sense for it to not be a Statement...
    //  merge Statement and Expression? Or make it a statement back? Or consider it as a Block?
    Assignment(
        /// prelude
        Vec<Statement>,
        /// Target
        Target,
        /// value
        Value,
    ),
    Block(Block),
    Boolean(bool),
    Symbol(SymbolId),
    ExprId(
        /// prelude
        Vec<Statement>,
        /// value
        ExprId,
    ),
    Number(i64),
    // todo:performance avoid copy
    String(String),
    Access(
        /// prelude
        Vec<Statement>,
        /// value
        Value,
        /// symbol in the value
        SymbolId,
    ),
    Call(
        /// prelude
        Vec<Statement>,
        /// called function
        SymbolId,
        /// parameters
        Vec<Value>,
    ),
    StructInstantiation(
        /// prelude
        Vec<Statement>,
        /// temp. variable
        ExprId,
        /// instantiated struct
        SymbolId,
        /// field values
        Vec<(SymbolId, Value)>,
    ),
    ArrayInstantiation(
        /// prelude
        Vec<Statement>,
        /// temp. variable
        ExprId,
        /// Element type ID
        TypeId,
        /// values
        Vec<Value>,
    ),
    ArrayAccess(
        /// prelude
        Vec<Statement>,
        /// target
        Value,
        /// index
        ExprId,
    ),
    If(
        /// prelude
        Vec<Statement>,
        /// condition
        Value,
        /// true block
        Block,
        /// false block
        Option<Block>,
    ),
    While(
        /// prelude
        Vec<Statement>,
        /// condition
        Value,
        /// body
        Block,
    ),
}

macro_rules! unop {
    ($op:expr, $params:expr, $codegen:expr) => {{
        debug_assert_eq!($params.len(), 1);
        if $params[0].is_binary_op($codegen) || $params[0].is_unary_op($codegen) {
            format!(
                "({op} {val})",
                op = $op,
                val = $params.get(0).unwrap().gen_c($codegen),
            )
        } else {
            format!(
                "{op} {val}",
                op = $op,
                val = $params.get(0).unwrap().gen_c($codegen),
            )
        }
    }};
}

macro_rules! binop {
    ($op:expr, $params:expr, $codegen:expr) => {{
        debug_assert_eq!($params.len(), 2);

        let left = if $params[0].is_binary_op($codegen) || $params[0].is_unary_op($codegen) {
            format!("({})", $params.get(0).unwrap().gen_c($codegen)).into()
        } else {
            $params.get(0).unwrap().gen_c($codegen)
        };

        let right = if $params[0].is_binary_op($codegen) || $params[0].is_unary_op($codegen) {
            format!("({})", $params.get(1).unwrap().gen_c($codegen)).into()
        } else {
            $params.get(1).unwrap().gen_c($codegen)
        };

        format!("{left} {op} {right}", op = $op,)
    }};
}

impl Expression {
    fn is_unary_op(&self, codegen: &CCodegen) -> bool {
        if let Expression::Call(_, f, ..) = self &&
            let SymbolKind::Native(_, _, _, k) = &codegen.mir.symbols[*f].kind {
                return k.is_unary_op();
        }
        false
    }

    fn is_binary_op(&self, codegen: &CCodegen) -> bool {
        if let Expression::Call(_, f, ..) = self
            && let SymbolKind::Native(_, _, _, k) = &codegen.mir.symbols[*f].kind {
            return k.is_binary_op();
        }
        false
    }

    #[cfg(debug_assertions)]
    fn has_prelude(&self) -> bool {
        match self {
            Expression::Intrinsic(..) => false,
            Expression::Assignment(prelude, ..)
            | Expression::ExprId(prelude, ..)
            | Expression::Access(prelude, ..)
            | Expression::Call(prelude, ..)
            | Expression::StructInstantiation(prelude, ..)
            | Expression::ArrayInstantiation(prelude, ..)
            | Expression::ArrayAccess(prelude, ..)
            | Expression::If(prelude, ..)
            | Expression::While(prelude, ..) => !prelude.is_empty(),
            Expression::Block(block) => block.statements.iter().any(|s| s.has_prelude()),
            Expression::Boolean(..)
            | Expression::Symbol(..)
            | Expression::Number(..)
            | Expression::String(..) => false,
        }
    }

    fn take_prelude(&mut self) -> Vec<Statement> {
        match self {
            Expression::Intrinsic(..) => Vec::new(),
            Expression::Assignment(prelude, ..)
            | Expression::ExprId(prelude, ..)
            | Expression::Access(prelude, ..)
            | Expression::Call(prelude, ..)
            | Expression::StructInstantiation(prelude, ..)
            | Expression::ArrayInstantiation(prelude, ..)
            | Expression::ArrayAccess(prelude, ..)
            | Expression::If(prelude, ..)
            | Expression::While(prelude, ..) => mem::take(prelude),
            Expression::Block(block) => block.statements.iter_mut().map(|s| s.take_prelude()).fold(
                Vec::new(),
                |mut acc, mut c| {
                    acc.append(&mut c);
                    acc
                },
            ),
            Expression::Boolean(..)
            | Expression::Symbol(..)
            | Expression::Number(..)
            | Expression::String(..) => vec![],
        }
    }

    fn need_semi(&self) -> bool {
        match self {
            Expression::Intrinsic(..) => false,
            Expression::Assignment(..) => true,
            Expression::Block(..) => false,
            Expression::Boolean(..) => true,
            Expression::Symbol(..) => true,
            Expression::ExprId(..) => true,
            Expression::Number(..) => true,
            Expression::String(..) => true,
            Expression::Access(..) => true,
            Expression::Call(..) => true,
            Expression::StructInstantiation(..) => false,
            Expression::ArrayInstantiation(..) => false,
            Expression::ArrayAccess(..) => true,
            Expression::If(..) => false,
            Expression::While(..) => false,
        }
    }

    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        match self {
            Expression::Intrinsic(intrinsic) => Self::gen_intrinsic(codegen, intrinsic),
            Expression::Assignment(prelude, target, value) => {
                Self::gen_assignment(codegen, prelude, target, value)
            }
            Expression::Block(block) => block.gen_c(codegen),
            Expression::Boolean(b) => b.to_string().into(),
            Expression::Symbol(sid) => match codegen.mir.symbols[*sid].kind {
                SymbolKind::Let => format!("me.{}", codegen.symbol_name(sid)).into(),
                SymbolKind::LetFn(..) => todo!(),
                SymbolKind::Parameter(..) => codegen.symbol_name(sid).into(),
                SymbolKind::Struct => todo!(),
                SymbolKind::Field(..) => todo!(),
                SymbolKind::NativeType(..) => todo!(),
                SymbolKind::Native(..) => todo!(),
            },
            Expression::ExprId(prelude, eid) => Self::gen_expr_id(codegen, prelude, eid),
            Expression::Number(n) => n.to_string().into(),
            Expression::String(s) => format!(
                "(sN3stdN3str6string*)tmc_stdlib_string_new((uint8_t*)\"{}\", {})",
                CCodegen::escape(s.as_str()),
                s.len()
            )
            .into(),
            Expression::Access(prelude, value, sid) => {
                Self::gen_access(codegen, prelude, value, *sid)
            }
            Expression::Call(prelude, sid, values) => {
                Self::gen_function_call(codegen, prelude, *sid, values)
            }
            Expression::StructInstantiation(prelude, eid, sid, fields) => {
                Self::gen_struct_instantiation(codegen, prelude, *eid, *sid, fields)
            }
            Expression::ArrayInstantiation(prelude, eid, element_tid, values) => {
                Self::gen_array_instantiation(codegen, prelude, *eid, *element_tid, values)
            }
            Expression::ArrayAccess(prelude, target, index) => {
                Self::gen_array_access(codegen, prelude, target, *index)
            }
            Expression::If(prelude, cond, true_block, false_block) => {
                Self::gen_if(codegen, prelude, cond, true_block, false_block)
            }
            Expression::While(prelude, cond, body) => Self::gen_while(codegen, prelude, cond, body),
        }
    }

    fn gen_intrinsic(_codegen: &CCodegen, intrinsic: &Intrinsic) -> CCode {
        match intrinsic {
            Intrinsic::CheckArrayIndex(index, length, line, column) => {
                format!("tmc_check_array_index(me.e{index}, {length}, {line}, {column});").into()
            }
        }
    }

    fn gen_assignment(
        codegen: &CCodegen,
        prelude: &[Statement],
        target: &Target,
        value: &Value,
    ) -> CCode {
        #[cfg(debug_assertions)]
        debug_assert!(!value.has_prelude());

        let mut prelude = codegen.gen_c(prelude).0;

        prelude.push_str(
            format!(
                include_str!("tmpl/expression-assignment.txt"),
                target = target.gen_c(codegen),
                value = value.gen_c(codegen),
            )
            .as_str(),
        );

        prelude.into()
    }

    fn gen_expr_id(codegen: &CCodegen, prelude: &[Statement], eid: &ExprId) -> CCode {
        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(format!("me.e{eid}").as_str());
        prelude.into()
    }

    fn gen_access(
        codegen: &CCodegen,
        prelude: &[Statement],
        value: &Value,
        sid: SymbolId,
    ) -> CCode {
        #[cfg(debug_assertions)]
        debug_assert!(!value.has_prelude());

        let mut prelude = codegen.gen_c(prelude).0;

        prelude.push_str(
            format!(
                include_str!("tmpl/expression-struct-field-access.txt"),
                value = value.gen_c(codegen),
                field = codegen.symbol_name(&sid)
            )
            .as_str(),
        );

        prelude.into()
    }

    fn gen_function_call(
        codegen: &CCodegen,
        prelude: &[Statement],
        sid: SymbolId,
        values: &[Value],
    ) -> CCode {
        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(
            match &codegen.mir.symbols[sid].kind {
                SymbolKind::LetFn(_, _, _) => {
                    let parameters = values
                        .iter()
                        .map(|value| {
                            #[cfg(debug_assertions)]
                            debug_assert!(!value.has_prelude());
                            value.gen_c(codegen)
                        })
                        .fold(String::new(), |mut acc, e| {
                            if !acc.is_empty() {
                                acc.push_str(", ");
                            }
                            acc.push_str(e.as_str());
                            acc
                        });

                    debug_assert_eq!(
                        codegen.functions[&sid].gen_parent_parameter,
                        codegen.functions[&sid].must_generate_frame()
                    );

                    if codegen.functions[&sid].gen_parent_parameter {
                        if values.is_empty() {
                            format!(
                                include_str!("tmpl/expression-function-call-noparameters.txt"),
                                name = codegen.symbol_name(&sid),
                            )
                        } else {
                            format!(
                                include_str!("tmpl/expression-function-call.txt"),
                                name = codegen.symbol_name(&sid),
                                parameters = parameters
                            )
                        }
                    } else {
                        format!(
                            include_str!("tmpl/expression-function-call-noframe.txt"),
                            name = codegen.symbol_name(&sid),
                            parameters = parameters
                        )
                    }
                }
                SymbolKind::Native(_, _, _, op) if op.is_unary_op() => {
                    unop!(op.op(), values, codegen)
                }
                SymbolKind::Native(_, _, _, op) if op.is_binary_op() => {
                    binop!(op.op(), values, codegen)
                }
                _ => panic!("function expected"),
            }
            .as_str(),
        );
        prelude.into()
    }

    fn gen_struct_instantiation(
        codegen: &CCodegen,
        prelude: &[Statement],
        eid: ExprId,
        sid: SymbolId,
        fields: &[(SymbolId, Value)],
    ) -> CCode {
        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(
            format!(
                include_str!("tmpl/expression-struct-instantiation.txt"),
                struct_name = codegen.symbol_name(&sid),
                eid = eid,
            )
            .as_str(),
        );

        for (sid, value) in fields.iter() {
            #[cfg(debug_assertions)]
            debug_assert!(!value.has_prelude());

            prelude.push_str(
                format!(
                    include_str!("tmpl/expression-struct-instantiation-field.txt"),
                    eid = eid,
                    field = codegen.symbol_name(sid),
                    value = value.gen_c(codegen)
                )
                .as_str(),
            )
        }

        prelude.into()
    }

    fn gen_array_instantiation(
        codegen: &CCodegen,
        prelude: &[Statement],
        eid: ExprId,
        element_tid: TypeId,
        values: &[Value],
    ) -> CCode {
        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(
            format!(
                include_str!("tmpl/expression-array-instantiation.txt"),
                eid = eid,
                len = values.len(),
                element_type = codegen.types[&element_tid].gen_c(codegen).as_str().trim()
            )
            .as_str(),
        );

        for (idx, value) in values.iter().enumerate() {
            #[cfg(debug_assertions)]
            debug_assert!(!value.has_prelude());

            prelude.push_str(
                format!(
                    include_str!("tmpl/expression-array-instantiation-field.txt"),
                    eid = eid,
                    index = idx,
                    value = value.gen_c(codegen)
                )
                .as_str(),
            )
        }

        prelude.into()
    }

    fn gen_array_access(
        codegen: &CCodegen,
        prelude: &[Statement],
        target: &Value,
        index: ExprId,
    ) -> CCode {
        #[cfg(debug_assertions)]
        debug_assert!(!target.has_prelude());

        let mut prelude = codegen.gen_c(prelude).0;

        prelude.push_str(
            format!(
                include_str!("tmpl/expression-array-access.txt"),
                target = target.gen_c(codegen),
                index = format!("me.e{index}").as_str(),
            )
            .as_str(),
        );

        prelude.into()
    }

    fn gen_if(
        codegen: &CCodegen,
        prelude: &[Statement],
        cond: &Value,
        true_block: &Block,
        false_block: &Option<Block>,
    ) -> CCode {
        #[cfg(debug_assertions)]
        debug_assert!(!cond.has_prelude());

        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(
            if let Some(false_block) = false_block {
                format!(
                    include_str!("tmpl/expression-if-else.txt"),
                    condition = cond.gen_c(codegen),
                    true_block = true_block.gen_c(codegen),
                    false_block = false_block.gen_c(codegen)
                )
            } else {
                format!(
                    include_str!("tmpl/expression-if.txt"),
                    condition = cond.gen_c(codegen),
                    true_block = true_block.gen_c(codegen),
                )
            }
            .as_str(),
        );
        prelude.into()
    }

    fn gen_while(codegen: &CCodegen, prelude: &[Statement], cond: &Value, body: &Block) -> CCode {
        #[cfg(debug_assertions)]
        debug_assert!(!cond.has_prelude());

        let mut prelude = codegen.gen_c(prelude).0;
        prelude.push_str(
            format!(
                include_str!("tmpl/expression-while.txt"),
                condition = cond.gen_c(codegen),
                body = body.gen_c(codegen),
            )
            .as_str(),
        );
        prelude.into()
    }

    fn into_block(self) -> Block {
        match self {
            Expression::Block(block) => block,
            _ => panic!("expression must be a block"),
        }
    }
}

#[derive(Debug)]
enum Intrinsic {
    CheckArrayIndex(
        /// index
        ExprId,
        /// array length
        usize,
        /// line
        usize,
        /// column
        usize,
    ),
}

#[derive(Debug)]
enum Value {
    Expression(Box<Expression>),
    Variable(ExprId),
}

impl Value {
    fn gen_c(&self, codegen: &CCodegen) -> CCode {
        match self {
            Value::Expression(e) => e.gen_c(codegen),
            Value::Variable(eid) => format!("me.e{eid}").into(),
        }
    }

    fn is_unary_op(&self, codegen: &CCodegen) -> bool {
        match self {
            Value::Expression(e) => e.is_unary_op(codegen),
            Value::Variable(_) => false,
        }
    }

    fn is_binary_op(&self, codegen: &CCodegen) -> bool {
        match self {
            Value::Expression(e) => e.is_binary_op(codegen),
            Value::Variable(_) => false,
        }
    }

    #[cfg(debug_assertions)]
    fn has_prelude(&self) -> bool {
        match self {
            Value::Expression(e) => e.has_prelude(),
            Value::Variable(_) => false,
        }
    }
}

#[derive(Debug)]
struct Struct {
    /// The symbol holding the struct's name (from CCodegen.mangled_names)
    symbol: SymbolId,
    /// The struct fields
    fields: Vec<SymbolId>,
}

impl Struct {
    fn gen_declaration(&self, codegen: &CCodegen) -> CCode {
        format!(
            include_str!("tmpl/struct-declaration.txt"),
            name = codegen.symbol_name(&self.symbol),
        )
        .into()
    }

    fn gen_definition(&self, codegen: &CCodegen) -> CCode {
        if self.fields.is_empty() {
            format!(
                include_str!("tmpl/struct-empty-definition.txt"),
                name = codegen.symbol_name(&self.symbol),
            )
            .into()
        } else {
            let fields = self
                .fields
                .iter()
                .map(|sid| {
                    format!(
                        include_str!("tmpl/struct-field.txt"),
                        type = codegen.symbol_type_c(sid),
                        name = codegen.symbol_name(sid)
                    )
                })
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                });
            format!(
                include_str!("tmpl/struct-definition.txt"),
                name = codegen.symbol_name(&self.symbol),
                fields = fields.trim_end()
            )
            .into()
        }
    }
}

pub fn codegen(mir: Mir) -> Result<CCode, Diagnostics<()>> {
    let mut codegen = CCodegen::new(&mir);

    codegen.codegen()
}

impl<'mir> CCodegen<'mir> {
    fn new(mir: &'mir Mir) -> Self {
        Self {
            mir,
            mangled_names: Default::default(),
            types: Default::default(),
            structs: Default::default(),
            functions: Default::default(),
        }
    }

    fn gen_c(&self, statements: &[Statement]) -> CCode {
        CCode(
            statements
                .iter()
                .map(|statement| statement.gen_c(self))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                }),
        )
    }

    fn codegen(&mut self) -> Result<CCode, Diagnostics<()>> {
        self.collect_types();
        self.collect_structs();
        self.collect_functions();

        let mut structs = self.structs.values().collect::<Vec<_>>();
        structs.sort_by_key(|s| s.symbol);

        let struct_declarations =
            structs
                .iter()
                .map(|s| s.gen_declaration(self))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                });

        let struct_definitions =
            structs
                .iter()
                .map(|s| s.gen_definition(self))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                });

        let mut functions = self.functions.values().collect::<Vec<_>>();
        functions.sort_by_key(|s| s.symbol);

        let function_declarations =
            functions
                .iter()
                .map(|f| f.gen_declaration(self))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                });

        let function_frames =
            functions
                .iter()
                .filter_map(|f| f.gen_frame(self))
                .fold(String::new(), |mut acc, e| {
                    acc.push_str(e.as_str());
                    acc
                });

        let function_definitions = functions
            .iter()
            .filter_map(|f| f.gen_definition(self))
            .fold(String::new(), |mut acc, e| {
                acc.push_str(e.as_str());
                acc
            });

        Ok(format!(
            include_str!("tmpl/source.txt"),
            struct_declarations = struct_declarations.trim(),
            struct_definitions = struct_definitions.trim(),
            function_declarations = function_declarations.trim(),
            function_frames = function_frames.trim(),
            function_definitions = function_definitions.trim(),
        )
        .into())
    }

    fn collect_types(&mut self) {
        for (tid, ty) in self.mir.types.iter() {
            match &ty {
                MirType::Boolean => {
                    self.types.insert(tid, Type::Value("bool"));
                }
                MirType::Number => {
                    self.types.insert(tid, Type::Value("int64_t"));
                }
                MirType::Function(_, _) => {
                    // todo: implement
                }
                MirType::Struct(sid, _) => {
                    self.types.insert(tid, Type::SymbolPointer(*sid));
                }
                MirType::Array(element_tid, _len) => {
                    self.types.insert(tid, Type::Array(*element_tid));
                }
                MirType::Void => {
                    self.types.insert(tid, Type::Value("void"));
                }
                MirType::None => {
                    // todo understand why the following assert fails:
                    // debug_assert_eq!(none, 0);
                }
            }
        }
    }

    fn collect_structs(&mut self) {
        for (sid, s) in self.mir.structs.iter() {
            self.mangled_names.insert(
                s.symbol_id,
                Cow::Owned(mangle_struct_name(self.mir, sid, s.symbol_id)),
            );

            for field in s.fields.as_deref().unwrap_or_default() {
                self.mangled_names.insert(
                    field.symbol_id,
                    Cow::Borrowed(&self.mir.identifiers[field.identifier.id]),
                );
            }
        }

        self.structs.reserve(self.mir.structs.len());

        for (_sid, s) in self.mir.structs.iter() {
            self.structs.insert(
                s.symbol_id,
                Struct {
                    symbol: s.symbol_id,
                    fields: s
                        .fields
                        .as_deref()
                        .unwrap_or_default()
                        .iter()
                        .map(|field| field.symbol_id)
                        .collect(),
                },
            );
        }
    }

    fn collect_functions(&mut self) {
        self.functions.reserve(self.mir.functions.len());

        // first we mangle the functions and their parameters and variables names
        for (_, f) in self.mir.functions.iter() {
            let mut parameter_types = Vec::with_capacity(f.parameters.len());
            for parameter in f.parameters.iter() {
                self.mangled_names.insert(
                    parameter.symbol_id,
                    format!(
                        "{}_{}",
                        self.mir.identifiers[parameter.identifier.id], parameter.symbol_id
                    )
                    .into(),
                );

                parameter_types.push(parameter.type_id);
            }
            for (sid, _) in f.variables.iter() {
                self.mangled_names.insert(
                    *sid,
                    format!(
                        "{}_{sid}",
                        self.mir.identifiers[self.mir.symbols[*sid].ident_id]
                    )
                    .into(),
                );
            }

            self.mangled_names.insert(
                f.symbol_id,
                mangle_function_name(self.mir, f.identifier.id, &parameter_types, f.parent).into(),
            );
        }

        // then, we generate the functions declarations and definitions
        for (_fid, f) in self.mir.functions.iter() {
            let (block, variables) = f
                .body
                .map(|body| {
                    let t = self.transform_expression(body, None);
                    (t.element.into_block(), t.variables)
                })
                .unzip();

            self.functions.insert(
                f.symbol_id,
                Function {
                    symbol: f.symbol_id,
                    return_type: f.ret,
                    parameters: f.parameters.iter().map(|p| p.symbol_id).collect(),
                    variables: f.variables.keys().copied().collect(),
                    expressions: variables.unwrap_or_default(),
                    block,
                    gen_parent_parameter: f.body.is_some(),
                },
            );
        }
    }

    fn transform_expression<E: Into<ExprId>>(
        &self,
        expr_id: E,
        variable: Option<ExprId>,
    ) -> Transformed<Expression> {
        let expr_id = expr_id.into();
        match &self.mir.expressions[expr_id].kind {
            ExpressionKind::Assignment(target, eid) => {
                debug_assert!(variable.is_none());
                self.transform_assignment(*target, *eid)
            }
            ExpressionKind::If(cond_eid, true_eid, false_eid) => {
                self.transform_if(*cond_eid, *true_eid, *false_eid, variable)
            }
            ExpressionKind::Literal(literal) => {
                debug_assert!(variable.is_none());
                self.transform_literal(literal)
            }
            ExpressionKind::Access(eid, sid) => {
                debug_assert!(variable.is_none());
                self.transform_access(eid, sid)
            }
            ExpressionKind::FunctionCall(sid, eids) => {
                debug_assert!(variable.is_none());
                self.transform_function_call(*sid, eids)
            }
            ExpressionKind::While(cond_eid, body_eid) => {
                self.transform_while(*cond_eid, *body_eid, variable)
            }
            ExpressionKind::Block(eids) => {
                assert!(variable.is_none());
                let t = self.transform_block(eids, None);
                Transformed {
                    element: Expression::Block(t.element),
                    variables: t.variables,
                }
            }
            ExpressionKind::StructInstantiation(sid, _, fields) => {
                self.transform_struct_instantiation(expr_id, *sid, fields, variable)
            }
            ExpressionKind::ArrayInstantiation(eids) => {
                let tid = self
                    .mir
                    .expression_type_id(eids.first().expect("at least one element"));
                self.transform_array_instantiation(expr_id, tid, eids, variable)
            }
            ExpressionKind::ArrayAccess(target_eid, index_eid) => {
                debug_assert!(variable.is_none());
                self.transform_array_access(*target_eid, *index_eid)
            }
        }
    }

    fn transform_assignment(&self, target: MirTarget, eid: ExprId) -> Transformed<Expression> {
        let (prelude, value, mut expr_variables) = if self.mir.expressions[eid].is_c_statement() {
            let mut t = self.transform_expression(eid, Some(eid));
            t.variables.push(eid);
            (
                vec![Statement::Expression(t.element)],
                Value::Variable(eid),
                t.variables,
            )
        } else {
            let mut t = self.transform_expression(eid, None);
            (
                t.element.take_prelude(),
                Value::Expression(Box::new(t.element)),
                t.variables,
            )
        };

        let target = match target {
            MirTarget::Direct(sid) => Target::Symbol(sid),
            MirTarget::Indirect(target_eid) => {
                let mut t = self.transform_expression(target_eid, None);
                expr_variables.append(&mut t.variables);
                Target::Exp(Box::new(t.element))
            }
        };

        Transformed {
            element: Expression::Assignment(prelude, target, value),
            variables: expr_variables,
        }
    }

    fn transform_if(
        &self,
        cond_eid: ExprId,
        true_eid: ExprId,
        false_eid: Option<ExprId>,
        variable: Option<ExprId>,
    ) -> Transformed<Expression> {
        // todo:refactor c-prelude
        let (prelude, cond, mut cond_variables) = if self.mir.expressions[cond_eid].is_c_statement()
        {
            let mut t = self.transform_expression(cond_eid, Some(cond_eid));
            t.variables.push(cond_eid);
            (
                Some(Statement::Expression(t.element)),
                Value::Variable(cond_eid),
                t.variables,
            )
        } else {
            let t = self.transform_expression(cond_eid, None);
            (None, Value::Expression(Box::new(t.element)), vec![])
        };

        let mut true_t = self.transform_block(self.mir.expressions[true_eid].as_block(), variable);
        let mut false_t = false_eid
            .map(|eid| self.transform_block(self.mir.expressions[eid].as_block(), variable));

        true_t.variables.append(&mut cond_variables);
        if let Some(false_variables) = false_t.as_mut().map(|t| &mut t.variables) {
            true_t.variables.append(false_variables);
        }

        Transformed {
            element: Expression::If(
                prelude.map(|s| vec![s]).unwrap_or_default(),
                cond,
                true_t.element,
                false_t.map(|t| t.element),
            ),
            variables: true_t.variables,
        }
    }

    fn transform_literal(&self, literal: &Literal) -> Transformed<Expression> {
        match &literal.kind {
            LiteralKind::Boolean(value) => Transformed {
                element: Expression::Boolean(*value),
                variables: vec![],
            },
            LiteralKind::Identifier(sid) => Transformed {
                element: Expression::Symbol(*sid),
                variables: vec![],
            },
            LiteralKind::Number(value) => Transformed {
                element: Expression::Number(*value),
                variables: vec![],
            },
            LiteralKind::String(value) => Transformed {
                element: Expression::String(value.clone()),
                variables: vec![],
            },
        }
    }

    fn transform_access(&self, eid: &ExprId, sid: &SymbolId) -> Transformed<Expression> {
        let (prelude, value, variables) = if self.mir.expressions[*eid].is_c_statement() {
            let mut t = self.transform_expression(eid, Some(*eid));
            t.variables.push(*eid);
            let mut prelude = t.element.take_prelude();
            prelude.push(Statement::Expression(t.element));
            (prelude, Value::Variable(*eid), t.variables)
        } else {
            let mut t = self.transform_expression(eid, None);
            (
                t.element.take_prelude(),
                Value::Expression(Box::new(t.element)),
                t.variables,
            )
        };

        Transformed {
            element: Expression::Access(prelude, value, *sid),
            variables,
        }
    }

    fn transform_function_call(
        &self,
        function_sid: SymbolId,
        parameters: &[ExprId],
    ) -> Transformed<Expression> {
        let mut prelude = vec![];
        let mut parameter_values = vec![];
        let mut variables = vec![];

        for expression in parameters.iter().map(|eid| &self.mir.expressions[*eid]) {
            if expression.is_c_statement() {
                let mut t = self.transform_expression(expression.id, Some(expression.id));
                prelude.append(&mut t.element.take_prelude());
                prelude.push(Statement::Expression(t.element));
                parameter_values.push(Value::Variable(expression.id));
                variables.append(&mut t.variables);
                variables.push(expression.id);
            } else {
                let mut t = self.transform_expression(expression.id, None);
                prelude.append(&mut t.element.take_prelude());
                parameter_values.push(Value::Expression(Box::new(t.element)));
                variables.append(&mut t.variables);
            }
        }

        Transformed {
            element: Expression::Call(prelude, function_sid, parameter_values),
            variables,
        }
    }

    fn transform_while(
        &self,
        cond_eid: ExprId,
        body_eid: ExprId,
        variable: Option<ExprId>,
    ) -> Transformed<Expression> {
        let (prelude, cond, mut cond_variables) = if self.mir.expressions[cond_eid].is_c_statement()
        {
            let mut t = self.transform_expression(cond_eid, Some(cond_eid));
            t.variables.push(cond_eid);
            (
                Some(Statement::Expression(t.element)),
                Value::Variable(cond_eid),
                t.variables,
            )
        } else {
            let t = self.transform_expression(cond_eid, None);
            (None, Value::Expression(Box::new(t.element)), vec![])
        };

        let mut body_t = self.transform_block(self.mir.expressions[body_eid].as_block(), variable);
        body_t.variables.append(&mut cond_variables);

        Transformed {
            element: Expression::While(
                prelude.map(|s| vec![s]).unwrap_or_default(),
                cond,
                body_t.element,
            ),
            variables: body_t.variables,
        }
    }

    fn transform_block(&self, stmt_ids: &[StmtId], variable: Option<ExprId>) -> Transformed<Block> {
        let count = stmt_ids.len();
        let (statements, variables) = stmt_ids
            .iter()
            .enumerate()
            .map(|(i, stmt_id)| match &self.mir.statements[*stmt_id].kind {
                StatementKind::Expression(eid) => {
                    if let Some(variable) = variable
                        && i == count - 1
                    {
                        let mut t = self.transform_expression(eid, None);
                        let prelude = t.element.take_prelude();
                        (
                            Statement::Expression(Expression::Assignment(
                                prelude,
                                Target::Expression(variable),
                                Value::Expression(Box::new(t.element)),
                            )),
                            t.variables,
                        )
                    } else {
                        let t = self.transform_expression(eid, None);
                        (Statement::Expression(t.element), t.variables)
                    }
                }
                StatementKind::Ret(None) => (Statement::Return(vec![], None), vec![]),
                StatementKind::Ret(Some(eid)) => self.transform_ret_some(*eid),
            })
            .fold(
                (vec![], vec![]),
                |(mut statements_acc, mut variables_acc), (statement, mut variables)| {
                    statements_acc.push(statement);
                    variables_acc.append(&mut variables);
                    (statements_acc, variables_acc)
                },
            );

        Transformed {
            element: Block { statements },
            variables,
        }
    }

    fn transform_ret_some(&self, expr_id: ExprId) -> (Statement, Vec<ExprId>) {
        let (statements, value, variables) = if self.mir.expressions[expr_id].is_c_statement() {
            let mut t = self.transform_expression(expr_id, Some(expr_id));
            t.variables.push(expr_id);
            (
                vec![Statement::Expression(t.element)],
                Value::Variable(expr_id),
                t.variables,
            )
        } else {
            let mut t = self.transform_expression(expr_id, None);
            (
                t.element.take_prelude(),
                Value::Expression(Box::new(t.element)),
                t.variables,
            )
        };
        (Statement::Return(statements, Some(value)), variables)
    }

    fn transform_struct_instantiation(
        &self,
        eid: ExprId,
        struct_sid: SymbolId,
        fields: &[(SymbolId, ExprId)],
        variable: Option<ExprId>,
    ) -> Transformed<Expression> {
        let mut prelude = vec![];
        let mut field_values = vec![];
        let mut variables = vec![];

        for (field_sid, expression) in fields
            .iter()
            .map(|(field_sid, eid)| (*field_sid, &self.mir.expressions[*eid]))
        {
            if expression.is_c_statement() {
                let mut t = self.transform_expression(expression.id, None);
                prelude.push(Statement::Expression(t.element));
                field_values.push((field_sid, Value::Variable(expression.id)));
                variables.append(&mut t.variables);
            } else {
                let mut t = self.transform_expression(expression.id, None);
                field_values.push((field_sid, Value::Expression(Box::new(t.element))));
                variables.append(&mut t.variables);
            }
        }

        let struct_instantiation =
            Expression::StructInstantiation(prelude, eid, struct_sid, field_values);

        let tmp_variable = match variable {
            None => {
                variables.push(eid);
                eid
            }
            Some(variable) => variable,
        };

        Transformed {
            element: Expression::ExprId(
                vec![Statement::Expression(struct_instantiation)],
                tmp_variable,
            ),
            variables,
        }
    }

    fn transform_array_instantiation(
        &self,
        eid: ExprId,
        element_tid: TypeId,
        elements: &[ExprId],
        variable: Option<ExprId>,
    ) -> Transformed<Expression> {
        let mut prelude = vec![];
        let mut values = vec![];
        let mut variables = vec![];

        for expression in elements.iter().map(|eid| &self.mir.expressions[*eid]) {
            if expression.is_c_statement() {
                let mut t = self.transform_expression(expression.id, None);
                prelude.push(Statement::Expression(t.element));
                values.push(Value::Variable(expression.id));
                variables.append(&mut t.variables);
            } else {
                let mut t = self.transform_expression(expression.id, None);
                values.push(Value::Expression(Box::new(t.element)));
                variables.append(&mut t.variables);
            }
        }

        let tmp_variable = match variable {
            None => {
                variables.push(eid);
                eid
            }
            Some(variable) => variable,
        };

        let array_instantiation =
            Expression::ArrayInstantiation(prelude, tmp_variable, element_tid, values);

        // todo see if we can skip the ExprId when the array does not go somewhere (same for
        //  struct)
        Transformed {
            element: Expression::ExprId(
                vec![Statement::Expression(array_instantiation)],
                tmp_variable,
            ),
            variables,
        }
    }

    fn transform_array_access(
        &self,
        target_eid: ExprId,
        index_eid: ExprId,
    ) -> Transformed<Expression> {
        let mut prelude = vec![];
        let mut variables = vec![];

        let target_value = if self.mir.expressions[target_eid].is_c_statement() {
            let mut t = self.transform_expression(target_eid, Some(target_eid));
            prelude.append(&mut t.element.take_prelude());
            prelude.push(Statement::Expression(t.element));
            variables.push(target_eid);
            variables.append(&mut t.variables);
            Value::Variable(target_eid)
        } else {
            let mut t = self.transform_expression(target_eid, None);
            prelude.append(&mut t.element.take_prelude());
            variables.append(&mut t.variables);
            Value::Expression(Box::new(t.element))
        };

        let index_value = if self.mir.expressions[index_eid].is_c_statement() {
            let mut t = self.transform_expression(index_eid, Some(index_eid));
            prelude.append(&mut t.element.take_prelude());
            prelude.push(Statement::Expression(t.element));
            variables.push(index_eid);
            variables.append(&mut t.variables);
            index_eid
        } else {
            let mut t = self.transform_expression(index_eid, None);
            prelude.append(&mut t.element.take_prelude());
            prelude.push(Statement::Expression(Expression::Assignment(
                vec![],
                Target::Expression(index_eid),
                Value::Expression(Box::new(t.element)),
            )));
            variables.push(index_eid);
            variables.append(&mut t.variables);
            index_eid
        };

        prelude.push(Statement::Expression(Expression::Intrinsic(
            Intrinsic::CheckArrayIndex(
                index_value,
                self.mir.expression_type(target_eid).as_array().1,
                self.mir.expressions[index_eid].span.line,
                self.mir.expressions[index_eid].span.column,
            ),
        )));

        Transformed {
            element: Expression::ArrayAccess(prelude, target_value, index_value),
            variables,
        }
    }

    fn escape(s: &str) -> String {
        s.replace("\\", "\\\\").replace("\"", "\\\"")
    }

    fn symbol_name(&self, symbol_id: &SymbolId) -> &str {
        &self.mangled_names[symbol_id]
    }

    fn symbol_type_c<S: Into<SymbolId>>(&self, symbol_id: S) -> CCode {
        self.type_c(&self.mir.symbol_type_id(symbol_id))
    }

    fn expression_type_c<E: Into<ExprId>>(&self, expr_id: E) -> CCode {
        self.type_c(&self.mir.expressions[expr_id.into()].type_id)
    }

    fn type_c(&self, type_id: &TypeId) -> CCode {
        self.types[type_id].gen_c(self)
    }
}

struct Context {
    /// the generated code buffer
    writer: String,
    /// the indent level
    indent: usize,
    /// are we at the start of the line?
    start_of_line: bool,
}

const INDENT: &str = "  ";
impl Write for Context {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        if self.start_of_line {
            for (i, line) in s.lines().enumerate() {
                if i > 0 {
                    self.writer.push('\n');
                }
                for _ in 0..self.indent {
                    self.writer.write_str(INDENT)?;
                }
                self.writer.write_str(line)?;
            }
            if s.ends_with('\n') {
                self.writer.write_str("\n")?;
            }
        } else {
            self.writer.write_str(s)?;
        }
        self.start_of_line = s.ends_with('\n');
        Ok(())
    }
}

impl Display for Context {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str(&self.writer)
    }
}

impl From<Context> for String {
    fn from(value: Context) -> Self {
        value.writer
    }
}

#[derive(Default)]
pub struct CCode(String);

impl CCode {
    fn indent(self) -> CCode {
        self.0
            .lines()
            .map(|l| format!("  {l}\n"))
            .fold(String::new(), |mut acc, e| {
                acc.push_str(e.as_str());
                acc
            })
            .into()
    }

    pub fn as_str(&self) -> &str {
        self.0.as_str()
    }
}

impl From<String> for CCode {
    fn from(value: String) -> Self {
        Self(value)
    }
}

impl From<&str> for CCode {
    fn from(value: &str) -> Self {
        Self::from(value.to_string())
    }
}

impl TryFrom<&Mir> for CCode {
    type Error = Diagnostics<()>;

    fn try_from(mir: &Mir) -> Result<Self, Self::Error> {
        CCodegen::new(mir).codegen()
    }
}

impl Display for CCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Debug for CCode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        Debug::fmt(&self.0, f)
    }
}

trait CExpression {
    fn is_c_statement(&self) -> bool;
}

trait COperator {
    fn is_unary_op(&self) -> bool;
    fn is_binary_op(&self) -> bool;
    fn op(&self) -> &'static str;
}

impl COperator for NativeFnKind {
    fn is_unary_op(&self) -> bool {
        matches!(self, NativeFnKind::NegNumber)
    }

    fn is_binary_op(&self) -> bool {
        !self.is_unary_op()
    }

    fn op(&self) -> &'static str {
        match self {
            NativeFnKind::NegNumber => "-",
            NativeFnKind::AddNumberNumber => "+",
            NativeFnKind::SubNumberNumber => "-",
            NativeFnKind::MulNumberNumber => "*",
            NativeFnKind::DivNumberNumber => "/",
            NativeFnKind::EqNumberNumber => "==",
            NativeFnKind::NeqNumberNumber => "!=",
            NativeFnKind::GtNumberNumber => ">",
            NativeFnKind::LtNumberNumber => "<",
            NativeFnKind::GeNumberNumber => ">=",
            NativeFnKind::LeNumberNumber => "<=",
            NativeFnKind::EqBooleanBoolean => "==",
            NativeFnKind::NeqBooleanBoolean => "!=",
        }
    }
}

impl CExpression for MirExpression {
    fn is_c_statement(&self) -> bool {
        match &self.kind {
            ExpressionKind::Assignment(_, _) => true,
            ExpressionKind::If(_, _, _) => true,
            ExpressionKind::Literal(_) => false,
            ExpressionKind::Access(_, _) => false,
            ExpressionKind::FunctionCall(_, _) => false,
            ExpressionKind::While(_, _) => true,
            ExpressionKind::Block(_) => true,
            ExpressionKind::StructInstantiation(_, _, _) => true,
            ExpressionKind::ArrayInstantiation(_) => true,
            ExpressionKind::ArrayAccess(_, _) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use insta::assert_snapshot;
    use transmute_ast::CompilationUnit;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_core::ids::InputId;
    use transmute_hir::Resolve;
    use transmute_nst::nodes::Nst;

    macro_rules! t {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let mut compilation_unit: CompilationUnit = Default::default();

                Parser::new(
                    &mut compilation_unit,
                    None,
                    Lexer::new(InputId::from(0), &format!("{}\nnamespace core {{}}", $src)),
                )
                .parse();

                let nst = Nst::from(compilation_unit.into_ast().unwrap());
                let hir = nst.resolve().unwrap();
                let mir = Mir::try_from(hir).unwrap();
                let c = CCode::try_from(&mir);
                assert_snapshot!(c.unwrap());
            }
        };
    }

    t!(struct_empty, "struct EmptyStruct {}");
    t!(
        struct_simple,
        "struct SimpleStruct { field1: number, field2: boolean }"
    );
    t!(
        struct_simple_instantiation,
        r#"
        struct SimpleStruct { field1: number, field2: boolean }
        let f() {
            SimpleStruct { field1: 1, field2: true };
        }
        "#
    );
    t!(
        struct_nested,
        "struct Inner { field: number } struct Outer { field: Inner }"
    );
    t!(struct_self_ref, "struct SelfRef { field: SelfRef, }");
    t!(
        struct_nested_instantiation,
        r#"
        struct Inner { field: number } struct Outer { field: Inner }
        let f() {
            Outer {
                field: Inner {
                    field: 1
                }
            };
        }
        "#
    );

    t!(array_simple_instantioon, "let f() { [1, 2]; }");
    t!(
        array_nested_instantion,
        r#"
        let f() {
            [[1, 2], [3, 4]];
        }
        "#
    );

    t!(
        array_of_structs,
        r#"
        struct Point { x: number, y: number }
        let f() {
            [
                Point { x: 1,  y: 2  },
                Point { x: 10, y: 20 }
            ];
        }
        "#
    );
    t!(
        array_of_stricts_access,
        r#"
        struct S { f: number }
        let f() {
            let s = [ S { f: 1 } ];
            s[0].f = 2;
        }
        "#
    );

    t!(
        struct_of_arrays,
        r#"
        struct Point { x: [number; 2], y: [number; 2] }
        let f() {
            Point { x: [1, 10], y: [2, 20] };
        }
        "#
    );

    t!(function_simple, "let f() {  }");
    t!(function_one_parameter, "let f(n: number) {  }");
    t!(
        function_native,
        "namespace std { annotation native; } @std.native let f(n: number) {  }"
    );

    t!(
        function_struct_parameter,
        "struct S { field: number } let f(s: S) {  }"
    );
    t!(
        function_struct_return,
        "struct S { field: number } let f(): S { S { field: 1 }; }"
    );
    t!(
        function_struct_return_field,
        "struct S { field: number } let f(): number { let s = S { field: 1 }; s.field; }"
    );
    t!(
        function_struct_return_field_inline,
        "struct S { field: number } let f(): number { S { field: 1 }.field; }"
    );

    t!(function_array_parameter, "let f(a: [number; 2]) {}");
    t!(function_array_return, "let f(): [number; 2] { [1, 2]; }");
    t!(
        function_array_return_element,
        "let f(): number { let a = [0]; a[0]; }"
    );
    t!(
        function_array_return_element_inline,
        "let f(): number { ret [1][0]; }"
    );
    t!(
        function_call_on_struct1,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let main() {
            S { f: 1, }.f();
        }
        "#
    );
    t!(
        function_call_on_struct2,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let main() {
            f(S { f: 1, } );
        }
        "#
    );
    t!(
        function_call_on_expression1,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let g(n: number) {}
        let main() {
            S { f: 1, }.f().g();
        }
        "#
    );
    t!(
        function_call_on_expression2,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let g(n: number) {}
        let main() {
            g(S { f: 1, }.f());
        }
        "#
    );
    t!(
        function_call_on_expression3,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let g(n: number) {}
        let main() {
            f(S { f: 1, }).g();
        }
        "#
    );
    t!(
        function_call_on_expression4,
        r#"
        struct S { f: number, }
        let f(s: S): number { s.f; }
        let g(n: number) {}
        let main() {
            g(f(S { f: 1, }));
        }
        "#
    );

    t!(assignment_simple, "let f() { let a = 1; }");
    t!(
        assignment_if,
        "let f() { let a = if true { 1; } else { 2; }; }"
    );
    t!(
        assignment_struct,
        r#"
        struct Point {
            x: number,
            y: number,
        }
        let f() {
            let a = Point {
                x: 0,
                y: 0,
            };
        }
        "#
    );
    t!(
        assignment_struct_of_struct,
        r#"
        struct Point {
            x: number,
            y: number,
        }
        struct Rect {
            a: Point,
            b: Point,
        }
        let f() {
            let a = Rect {
                a: Point {
                    x: 0,
                    y: 0,
                },
                b: Point {
                    x: 10,
                    y: 10,
                },
            };
        }
        "#
    );
    t!(
        struct_field_access,
        r#"
            struct S {
                f: number
            }
            let f() {
                let s = S { f: 1 };
                s.f;
            }
        "#
    );
    t!(
        assignment_struct_field,
        r#"
            struct S {
                f: number
            }
            let f() {
                let s = S { f: 1 };
                s.f = 2;
            }
        "#
    );
    t!(
        struct_field_read,
        r#"
            struct S {
                f: number
            }
            let f() {
                let s = S { f: 1 };
                let b = s.f;
            }
        "#
    );
    t!(
        struct_field_read_inline,
        r#"
            struct S {
                f: number
            }
            let f() {
                let a = S { f: 1 }.f;
            }
        "#
    );

    t!(array_element_access, "let f() { let a = [0]; a[0]; }");
    t!(
        assignment_array_element,
        "let f() { let a = [0]; a[0] = 1; }"
    );
    t!(
        array_access_expr,
        "let f() { let a = [0]; a[if true { 0; } else { 1; }] = 1; }"
    );
    t!(array_access_inline, "let f() { [0][0] = 1; }");
    t!(
        array_nested_access_inline,
        r#"
        let f() {
            let n = [
                [ 0,  1],
                [10, 11],
            ][0][0];
        }
        "#
    );
    t!(
        array_access_from_expression,
        "let f() { if true { [0]; } else { [0]; }[0] = 1; }"
    );
    t!(
        array_if,
        r#"
        let f() {
            let n = if true {
                [ 0, 2, 4 ];
            } else {
                [ 1, 3, 5 ];
            }[0];
        }
        "#
    );

    t!(number, "let f () { 1; }");
    t!(boolean_true, "let f () { true; }");
    t!(boolean_false, "let f () { false; }");
    t!(
        string,
        "namespace std { namespace str { struct string {} } } let f () { \"hello, world\"; }"
    );
    t!(
        string_with_double_quotes,
        "namespace std { namespace str { struct string {} } } let f () { \"\\\"quoted\\\"\"; }"
    );

    t!(parameter, "let f(n: number) { n; }");
    t!(variable, "let f() { let n = 0; n; }");

    t!(neg_number, "let f() { -1; }");

    t!(eq_number_number, "let f() { 1 == 1; }");
    t!(add_number_number, "let f() { 1 + 1; }");

    t!(sub_number_number, "let f() { 1 - 1; }");
    t!(mul_number_number, "let f() { 1 * 1; }");
    t!(div_number_number, "let f() { 1 / 1; }");
    t!(neq_number_number, "let f() { 1 != 1; }");
    t!(gt_number_number, "let f() { 1 > 1; }");
    t!(lt_number_number, "let f() { 1 < 1; }");
    t!(ge_number_number, "let f() { 1 >= 1; }");
    t!(le_number_number, "let f() { 1 <= 1; }");

    t!(
        binary_op_parents,
        "let f(a: number, b: number, c: number, d: number) { (a-b) * (c-d); }"
    );

    t!(eq_boolean_boolean, " let f() { true == true; }");
    t!(neq_boolean_boolean, " let f() { true != true; }");

    t!(if_simple, "let f(n: number) { if n == 1 { 1; } }");
    t!(
        if_with_else,
        "let f(n: number) { if n == 1 { 1; } else { 2; } }"
    );
    t!(
        if_as_expression,
        "let f(n: number) { n + if n == 1 { 1; } else { 2; }; }"
    );
    t!(
        if_as_expression_nested,
        "let f(n: number) { n + if if n == 1 { 1 == 1; } else {1 == 2; } { 1; } else { 2; }; }"
    );

    t!(while_simple, "let f(n: number) { while n == 1 { 1; } }");
    t!(
        while_as_expression,
        "let f(n: number) { n + while n == 1 { 1; }; }"
    );
    t!(
        while_as_expression_mested,
        "let f(n: number) { n + while while n == 1 { 1 == 1; } { 2; }; }"
    );

    t!(ret_void, "let f() { ret; }");
    t!(ret_number, "let f(): number { ret 1; }");
    t!(
        ret_if,
        "let f(): number { ret if 0 == 1 { 2; } else { 3; }; }"
    );
}
