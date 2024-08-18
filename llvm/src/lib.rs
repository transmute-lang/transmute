#![allow(dead_code)] // fixme eventually remove
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicMetadataTypeEnum, IntType, VoidType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue};
use inkwell::IntPredicate;
use transmute_core::error::Diagnostics;
use transmute_core::ids::ExprId;
use transmute_hir::expression::ExpressionKind;
use transmute_hir::literal::LiteralKind;
use transmute_hir::natives::{NativeFnKind, Type};
use transmute_hir::statement::StatementKind;
use transmute_hir::symbol::SymbolKind;
use transmute_hir::{
    ResolvedExpression, ResolvedHir, ResolvedIdentifier, ResolvedIdentifierRef, ResolvedParameter,
    ResolvedReturn, ResolvedStatement,
};

struct Codegen<'ctx> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    bool_type: IntType<'ctx>,
    i64_type: IntType<'ctx>,
    void_type: VoidType<'ctx>,
}

impl<'ctx> Codegen<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let module = context.create_module("main");
        let builder = context.create_builder();

        let bool_type = context.bool_type();
        let i64_type = context.i64_type();
        let void_type = context.void_type();

        let print_fn_type = void_type.fn_type(&[i64_type.into()], false);
        module.add_function("print", print_fn_type, None);

        Self {
            context,
            module,
            builder,
            bool_type,
            i64_type,
            void_type,
        }
    }

    pub fn gen(self, hir: &ResolvedHir) -> Result<Module<'ctx>, Diagnostics> {
        for stmt_id in hir.roots.iter() {
            self.gen_statement(hir, &hir.statements[*stmt_id]);
        }

        Ok(self.module)
    }

    fn gen_statement(&self, hir: &ResolvedHir, stmt: &ResolvedStatement) {
        match &stmt.kind {
            StatementKind::Expression(_) => todo!(),
            StatementKind::Let(_, _) => todo!(),
            StatementKind::Ret(expr_id, _ret_mode) => {
                self.gen_ret(hir, &hir.expressions[*expr_id]);
            }
            StatementKind::LetFn(ident, params, ret_type, expr_id) => {
                self.gen_function(hir, ident, params, ret_type, *expr_id)
            }
            StatementKind::Struct(_, _) => todo!(),
        }
    }

    fn gen_ret(&self, hir: &ResolvedHir, expr: &ResolvedExpression) {
        match self.gen_expression(hir, expr) {
            None => {
                // fixme a ret always has an expression, otherwise, no ret...
                self.builder.build_return(None).unwrap()
            }
            Some(BasicValueEnum::ArrayValue(_)) => todo!(),
            Some(BasicValueEnum::IntValue(val)) => self.builder.build_return(Some(&val)).unwrap(),
            Some(BasicValueEnum::FloatValue(_)) => todo!(),
            Some(BasicValueEnum::PointerValue(_)) => todo!(),
            Some(BasicValueEnum::StructValue(_)) => todo!(),
            Some(BasicValueEnum::VectorValue(_)) => todo!(),
        };
    }

    fn gen_function(
        &self,
        hir: &ResolvedHir,
        ident: &ResolvedIdentifier,
        params: &[ResolvedParameter],
        ret_type: &ResolvedReturn,
        expr_id: ExprId,
    ) {
        let parameters_types = params
            .iter()
            .map(|p| match &hir.types[p.resolved_type_id()] {
                Type::Invalid => todo!(),
                Type::Boolean => self.bool_type.into(),
                Type::Function(_, _) => todo!(),
                Type::Struct(_) => todo!(),
                Type::Number => self.i64_type.into(),
                Type::Void => todo!(),
                Type::None => todo!(),
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();

        let resolved_ret_type = &hir.types[ret_type.resolved_type_id()];
        let fn_type = match resolved_ret_type {
            Type::Invalid => todo!(),
            Type::Boolean => self.bool_type.fn_type(&parameters_types, false),
            Type::Function(_, _) => todo!(),
            Type::Struct(_) => todo!(),
            Type::Number => self.i64_type.fn_type(&parameters_types, false),
            Type::Void => self.void_type.fn_type(&parameters_types, false),
            Type::None => todo!(),
        };

        let function = self
            .module
            .add_function(&hir.identifiers[ident.id], fn_type, None);

        for (i, param) in function.get_param_iter().enumerate() {
            let name = &hir.identifiers[params[i].identifier.id];
            let name = format!("{}__#sym{}", name, params[i].resolved_symobl_id());
            match param {
                BasicValueEnum::ArrayValue(_) => todo!(),
                BasicValueEnum::IntValue(val) => val.set_name(&name),
                BasicValueEnum::FloatValue(_) => todo!(),
                BasicValueEnum::PointerValue(_) => todo!(),
                BasicValueEnum::StructValue(_) => todo!(),
                BasicValueEnum::VectorValue(_) => todo!(),
            }
        }

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        self.gen_expression(hir, &hir.expressions[expr_id]);
    }

    fn gen_expression(
        &self,
        hir: &ResolvedHir,
        expr: &ResolvedExpression,
    ) -> Option<BasicValueEnum<'ctx>> {
        match &expr.kind {
            ExpressionKind::Assignment(_, _) => todo!(),
            ExpressionKind::If(_, _, _) => todo!(),
            ExpressionKind::Literal(literal) => match &literal.kind {
                LiteralKind::Boolean(_) => todo!(),
                LiteralKind::Identifier(ident_ref_id) => {
                    self.gen_expression_ident(hir, &hir.identifier_refs[*ident_ref_id])
                }
                LiteralKind::Number(_) => todo!(),
            },
            ExpressionKind::Access(_, _) => todo!(),
            ExpressionKind::FunctionCall(ident_ref_id, params) => {
                self.gen_function_call(hir, &hir.identifier_refs[*ident_ref_id], params)
            }
            ExpressionKind::While(_, _) => todo!(),
            ExpressionKind::Block(stmt_ids) => {
                for stmt_id in stmt_ids {
                    self.gen_statement(hir, &hir.statements[*stmt_id]);
                }
                None
            }
            ExpressionKind::StructInstantiation(_, _) => todo!(),
        }
    }

    fn gen_expression_ident(
        &self,
        hir: &ResolvedHir,
        ident_ref: &ResolvedIdentifierRef,
    ) -> Option<BasicValueEnum<'ctx>> {
        match &hir.symbols[ident_ref.resolved_symbol_id()].kind {
            SymbolKind::NotFound => todo!(),
            SymbolKind::Let(_) => todo!(),
            SymbolKind::LetFn(_, _, _) => todo!(),
            SymbolKind::Parameter(_, index) => self.current_function().get_nth_param(*index as u32),
            SymbolKind::Struct(_) => todo!(),
            SymbolKind::Field(_, _) => todo!(),
            SymbolKind::NativeType(_, _) => todo!(),
            SymbolKind::Native(_, _, _, _) => todo!(),
        }
    }

    fn gen_function_call(
        &self,
        hir: &ResolvedHir,
        ident_ref: &ResolvedIdentifierRef,
        params: &[ExprId],
    ) -> Option<BasicValueEnum<'ctx>> {
        let symbol = &hir.symbols[(&hir.identifier_refs[ident_ref.id]).resolved_symbol_id()];
        if let SymbolKind::Native(_, _, _, kind) = &symbol.kind {
            if kind.is_instr() {
                return kind.gen_instr(hir, self, params);
            }
        }

        let parameters = params
            .iter()
            .map(|e| match self.gen_expression(hir, &hir.expressions[*e]) {
                None => panic!(),
                Some(BasicValueEnum::ArrayValue(_)) => todo!(),
                Some(BasicValueEnum::IntValue(val)) => BasicMetadataValueEnum::IntValue(val),
                Some(BasicValueEnum::FloatValue(_)) => todo!(),
                Some(BasicValueEnum::PointerValue(_)) => todo!(),
                Some(BasicValueEnum::StructValue(_)) => todo!(),
                Some(BasicValueEnum::VectorValue(_)) => todo!(),
            })
            .collect::<Vec<BasicMetadataValueEnum>>();

        let function_name = &hir.identifiers[ident_ref.ident.id];
        let called_function = self
            .module
            .get_function(function_name)
            .unwrap_or_else(|| panic!("called function `{}` exists", function_name));
        self.builder
            .build_call(
                called_function,
                &parameters,
                &format!("{function_name}__#res",),
            )
            .unwrap()
            .try_as_basic_value()
            .left()
    }

    fn current_function(&self) -> FunctionValue<'ctx> {
        self.builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap()
    }
}

trait LlvmImpl {
    fn is_instr(&self) -> bool;

    fn gen_instr<'ctx>(
        &self,
        hir: &ResolvedHir,
        codegen: &Codegen<'ctx>,
        params: &[ExprId],
    ) -> Option<BasicValueEnum<'ctx>>;
}

impl LlvmImpl for NativeFnKind {
    fn is_instr(&self) -> bool {
        match self {
            NativeFnKind::NegNumber => true,
            NativeFnKind::AddNumberNumber => true,
            NativeFnKind::SubNumberNumber => true,
            NativeFnKind::MulNumberNumber => true,
            NativeFnKind::DivNumberNumber => true,
            NativeFnKind::EqNumberNumber => true,
            NativeFnKind::NeqNumberNumber => true,
            NativeFnKind::GtNumberNumber => true,
            NativeFnKind::LtNumberNumber => true,
            NativeFnKind::GeNumberNumber => true,
            NativeFnKind::LeNumberNumber => true,
            NativeFnKind::EqBooleanBoolean => true,
            NativeFnKind::NeqBooleanBoolean => true,
            NativeFnKind::PrintNumber => false,
        }
    }

    fn gen_instr<'ctx>(
        &self,
        hir: &ResolvedHir,
        codegen: &Codegen<'ctx>,
        params: &[ExprId],
    ) -> Option<BasicValueEnum<'ctx>> {
        match self {
            NativeFnKind::NegNumber => todo!(),
            NativeFnKind::AddNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_add(lhs, rhs, "add")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::SubNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_sub(lhs, rhs, "sub")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::MulNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_mul(lhs, rhs, "mul")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::DivNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_signed_div(lhs, rhs, "div")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::EqNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::NeqNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ne")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::GtNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::LtNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::GeNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SGE, lhs, rhs, "ge")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::LeNumberNumber => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SGT, lhs, rhs, "le")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::EqBooleanBoolean => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::NeqBooleanBoolean => {
                let lhs = codegen
                    .gen_expression(hir, &hir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(hir, &hir.expressions[params[1]])
                    .unwrap()
                    .into_int_value();
                Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ne")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::PrintNumber => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Codegen;
    use inkwell::context::Context;
    use insta::assert_snapshot;
    use transmute_ast::lexer::Lexer;
    use transmute_ast::parser::Parser;
    use transmute_hir::natives::Natives;
    use transmute_hir::UnresolvedHir;

    macro_rules! gen {
        ($name:ident, $src:expr) => {
            #[test]
            fn $name() {
                let ast = Parser::new(Lexer::new($src)).parse().unwrap();
                let hir = UnresolvedHir::from(ast).resolve(Natives::new()).unwrap();

                let context = Context::create();
                let codegen = Codegen::new(&context);
                let res = codegen.gen(&hir).unwrap().print_to_string().to_string();

                assert_snapshot!(res);
            }
        };
    }

    gen!(add, "let f(l: number, r: number): number { l + r; }");
    gen!(sub, "let f(l: number, r: number): number { l - r; }");
    gen!(mul, "let f(l: number, r: number): number { l * r; }");
    gen!(div, "let f(l: number, r: number): number { l / r; }");
    gen!(
        eq_number_number,
        "let f(l: number, r: number): boolean { l == r; }"
    );
    gen!(
        ne_number_number,
        "let f(l: number, r: number): boolean { l != r; }"
    );
    gen!(lt, "let f(l: number, r: number): boolean { l < r; }");
    gen!(gt, "let f(l: number, r: number): boolean { l > r; }");
    gen!(le, "let f(l: number, r: number): boolean { l <= r; }");
    gen!(ge, "let f(l: number, r: number): boolean { l >= r; }");
    gen!(
        eq_boolean_boolean,
        "let f(l: boolean, r: boolean): boolean { l == r; }"
    );
    gen!(
        ne_boolean_boolean,
        "let f(l: boolean, r: boolean): boolean { l != r; }"
    );
    gen!(print, "let a(n: number) { print(n); }");

}
