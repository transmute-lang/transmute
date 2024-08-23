#![allow(dead_code)]

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, VoidType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::{IntPredicate, OptimizationLevel};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, SymbolId, TypeId};
use transmute_hir::expression::ExpressionKind;
use transmute_hir::expression::Target as AssignmentTarget;
use transmute_hir::literal::LiteralKind;
use transmute_hir::natives::{NativeFnKind, Type};
use transmute_hir::statement::StatementKind;
use transmute_hir::symbol::SymbolKind;
use transmute_hir::{
    ResolvedExpression, ResolvedHir, ResolvedIdentifier, ResolvedIdentifierRef, ResolvedParameter,
    ResolvedReturn, ResolvedStatement,
};

pub struct LlvmIrGen {
    context: Context,
    target_triple: TargetTriple,
}

impl LlvmIrGen {
    pub fn gen(&self, hir: &ResolvedHir) -> Result<LlvmIr, Diagnostics> {
        Target::initialize_all(&InitializationConfig::default());
        let target = Target::from_triple(&self.target_triple).unwrap();
        let target_machine = target
            .create_target_machine(
                &self.target_triple,
                "generic",
                "",
                OptimizationLevel::None,
                RelocMode::PIC,
                CodeModel::Default,
            )
            .unwrap();

        Codegen::new(&self.context, &self.target_triple, &target_machine)
            .gen(hir)
            .map(|module| LlvmIr {
                module,
                target_machine,
            })
    }
}

impl Default for LlvmIrGen {
    fn default() -> Self {
        Self {
            context: Context::create(),
            target_triple: TargetMachine::get_default_triple(),
        }
    }
}

pub struct LlvmIr<'ctx> {
    module: Module<'ctx>,
    target_machine: TargetMachine,
}

impl<'ctx> LlvmIr<'ctx> {
    // todo error handling
    pub fn build_bin<P: Into<PathBuf>>(&self, rt: &[u8], path: P) -> Result<(), Diagnostics> {
        let path = path.into();

        let crt_bitcode_path = path.with_file_name("crt.bc");
        fs::write(&crt_bitcode_path, rt).unwrap();

        let tm_object_path = path.clone().with_extension("o");
        self.target_machine
            .write_to_file(&self.module, FileType::Object, &tm_object_path)
            .unwrap();

        match Command::new("clang")
            .arg(&tm_object_path)
            .arg(&crt_bitcode_path)
            .arg("-o")
            .arg(path)
            .output()
        {
            Ok(_) => {
                println!("Done");
            }
            Err(err) => {
                eprintln!("{err}");
            }
        }

        fs::remove_file(crt_bitcode_path).unwrap();
        fs::remove_file(tm_object_path).unwrap();

        Ok(())
    }
}

struct Codegen<'ctx, 't> {
    context: &'ctx Context,
    module: Module<'ctx>,
    builder: Builder<'ctx>,
    bool_type: IntType<'ctx>,
    i64_type: IntType<'ctx>,
    void_type: VoidType<'ctx>,

    variables: HashMap<SymbolId, PointerValue<'ctx>>,

    target_triple: &'t TargetTriple,
    target_machine: &'t TargetMachine,
}

impl<'ctx, 't> Codegen<'ctx, 't> {
    pub fn new(
        context: &'ctx Context,
        target_triple: &'t TargetTriple,
        target_machine: &'t TargetMachine,
    ) -> Self {
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
            variables: HashMap::default(),
            target_triple,
            target_machine,
        }
    }

    pub fn gen(mut self, hir: &ResolvedHir) -> Result<Module<'ctx>, Diagnostics> {
        for stmt_id in hir.roots.iter() {
            self.gen_statement(hir, &hir.statements[*stmt_id]);
        }

        // println!("{}", self.module.to_string().as_str());
        #[cfg(not(test))]
        self.optimize();

        Ok(self.module)
    }

    fn optimize(&self) {
        let passes: &[&str] = &[
            "instcombine",
            "reassociate",
            "gvn",
            "simplifycfg",
            "mem2reg",
        ];

        self.module
            .set_data_layout(&self.target_machine.get_target_data().get_data_layout());
        self.module.set_triple(self.target_triple);

        self.module
            .run_passes(
                passes.join(",").as_str(),
                self.target_machine,
                PassBuilderOptions::create(),
            )
            .unwrap();

        // let path = fs::canonicalize(&PathBuf::from(".".to_string()))
        //     .unwrap()
        //     .parent()
        //     .unwrap()
        //     .join("exp");
        //
        // let ll_path = path.clone().join("assembly.ll");
        // self.module.print_to_file(ll_path).unwrap();
        //
        // let asm_path = path.clone().join("assembly.s");
        // println!("Writing assembly to {}", asm_path.display());
        // target_machine
        //     .write_to_file(&self.module, FileType::Assembly, &asm_path)
        //     .unwrap();
        //
        // let object_path = path.clone().join("object.o");
        // println!("Writing object to {}", asm_path.display());
        // target_machine
        //     .write_to_file(&self.module, FileType::Object, &object_path)
        //     .unwrap()
    }

    fn gen_statement(&mut self, hir: &ResolvedHir, stmt: &ResolvedStatement) -> Value<'ctx> {
        match &stmt.kind {
            StatementKind::Expression(expr_id) => {
                self.gen_expression(hir, &hir.expressions[*expr_id])
            }
            StatementKind::Let(ident, expr_id) => {
                self.gen_let(hir, ident, &hir.expressions[*expr_id])
            }
            StatementKind::Ret(expr_id, _ret_mode) => self.gen_ret(hir, &hir.expressions[*expr_id]),
            StatementKind::LetFn(ident, params, ret_type, expr_id) => {
                self.gen_function(hir, ident, params, ret_type, *expr_id)
            }
            StatementKind::Struct(_, _) => todo!(),
        }
    }

    fn gen_ret(&mut self, hir: &ResolvedHir, expr: &ResolvedExpression) -> Value<'ctx> {
        match self.gen_expression(hir, expr) {
            Value::Never => panic!(),
            Value::None => {
                // this is used for implicit ret, where we can return nothing.
                self.builder.build_return(None).unwrap();
            }
            Value::Some(BasicValueEnum::ArrayValue(_)) => todo!(),
            Value::Some(BasicValueEnum::IntValue(val)) => {
                self.builder.build_return(Some(&val)).unwrap();
            }
            Value::Some(BasicValueEnum::FloatValue(_)) => todo!(),
            Value::Some(BasicValueEnum::PointerValue(_)) => todo!(),
            Value::Some(BasicValueEnum::StructValue(_)) => todo!(),
            Value::Some(BasicValueEnum::VectorValue(_)) => todo!(),
        };
        Value::Never
    }

    fn gen_let(
        &mut self,
        hir: &ResolvedHir,
        ident: &ResolvedIdentifier,
        expr: &ResolvedExpression,
    ) -> Value<'ctx> {
        let symbol = &hir.symbols[ident.resolved_symbol_id()];
        let llvm_type = self.llvm_type(hir, symbol.type_id);

        let ptr = self.gen_alloca(
            llvm_type,
            &format!("{}#local#sym{}#", &hir.identifiers[ident.id], symbol.id),
            symbol.id,
            None,
        );

        let val = self.gen_expression(hir, expr).unwrap();
        self.builder.build_store(ptr, val).unwrap();

        Value::None
    }

    fn gen_function(
        &mut self,
        hir: &ResolvedHir,
        ident: &ResolvedIdentifier,
        params: &[ResolvedParameter],
        ret_type: &ResolvedReturn,
        expr_id: ExprId,
    ) -> Value<'ctx> {
        let parameters_types = params
            .iter()
            .map(|p| self.llvm_type(hir, p.resolved_type_id()).into())
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
        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        for (i, param) in function.get_param_iter().enumerate() {
            // todo name may be made of the form {name}#param#sym{sid}
            let name = format!("{}#sym{}#", &hir.identifiers[params[i].identifier.id], params[i].resolved_symobl_id());
            match param {
                BasicValueEnum::ArrayValue(_) => todo!(),
                BasicValueEnum::IntValue(val) => val.set_name(&name),
                BasicValueEnum::FloatValue(_) => todo!(),
                BasicValueEnum::PointerValue(_) => todo!(),
                BasicValueEnum::StructValue(_) => todo!(),
                BasicValueEnum::VectorValue(_) => todo!(),
            }
            // todo remove once we know what params are muted in function
            self.gen_alloca(
                param.get_type(),
                &format!("{}#local#sym{}#", &hir.identifiers[params[i].identifier.id], params[i].resolved_symobl_id()),
                params[i].resolved_symobl_id(),
                Some(param)
            );
        }

        self.gen_expression(hir, &hir.expressions[expr_id]);

        Value::None
    }

    fn gen_expression(&mut self, hir: &ResolvedHir, expr: &ResolvedExpression) -> Value<'ctx> {
        let value = match &expr.kind {
            ExpressionKind::Assignment(target, expr) => {
                self.gen_assignment(hir, target, &hir.expressions[*expr])
            }
            ExpressionKind::If(cond_expr_id, true_expr_id, false_expr_id) => self.gen_if(
                hir,
                &hir.expressions[*cond_expr_id],
                &hir.expressions[*true_expr_id],
                false_expr_id.map(|expr_id| &hir.expressions[expr_id]),
            ),
            ExpressionKind::Literal(literal) => match &literal.kind {
                LiteralKind::Boolean(bool) => {
                    Value::Some(self.bool_type.const_int(*bool as u64, false).into())
                }
                LiteralKind::Identifier(ident_ref_id) => {
                    Value::Some(self.gen_expression_ident(hir, &hir.identifier_refs[*ident_ref_id]))
                }
                LiteralKind::Number(number) => {
                    // todo check what happens for negative numbers
                    Value::Some(self.i64_type.const_int(*number as u64, false).into())
                }
            },
            ExpressionKind::Access(_, _) => todo!(),
            ExpressionKind::FunctionCall(ident_ref_id, params) => {
                self.gen_function_call(hir, &hir.identifier_refs[*ident_ref_id], params)
            }
            ExpressionKind::While(cond, body) => {
                self.gen_while(hir, &hir.expressions[*cond], &hir.expressions[*body])
            }
            ExpressionKind::Block(stmt_ids) => {
                let mut value = Value::None;
                for stmt_id in stmt_ids {
                    value = self.gen_statement(hir, &hir.statements[*stmt_id]);
                    if matches!(value, Value::Never) {
                        return value;
                    }
                }
                value
            }
            ExpressionKind::StructInstantiation(_, _) => todo!(),
        };

        #[cfg(debug_assertions)]
        {
            let t = &hir.types[expr.resolved_type_id()];
            debug_assert!(
                t != &Type::None && value != Value::Never
                    || t == &Type::None && value == Value::Never
            );
        }

        value
    }

    fn gen_assignment(
        &mut self,
        hir: &ResolvedHir,
        target: &AssignmentTarget,
        expr: &ResolvedExpression,
    ) -> Value<'ctx> {
        let ptr = match target {
            AssignmentTarget::Direct(ident_ref_id) => {
                let symbol_id = hir.identifier_refs[*ident_ref_id].resolved_symbol_id();

                #[allow(clippy::map_entry)]
                if !self.variables.contains_key(&symbol_id) {
                    match hir.symbols[symbol_id].kind {
                        SymbolKind::NotFound => todo!(),
                        SymbolKind::Let(_) => panic!("variable already exists"),
                        SymbolKind::LetFn(_, _, _) => todo!(),
                        SymbolKind::Parameter(_, index) => {
                            let param =
                                self.current_function().get_nth_param(index as u32).unwrap();
                            self.gen_alloca(
                                param.get_type(),
                                &format!(
                                    "{}#local#sym{}#",
                                    hir.identifiers[hir.identifier_refs[*ident_ref_id].ident.id],
                                    symbol_id
                                ),
                                symbol_id,
                                Some(param),
                            );
                        }
                        SymbolKind::Struct(_) => todo!(),
                        SymbolKind::Field(_, _) => todo!(),
                        SymbolKind::NativeType(_, _) => todo!(),
                        SymbolKind::Native(_, _, _, _) => todo!(),
                    }
                }
                self.variables[&symbol_id]
            }
            AssignmentTarget::Indirect(_) => todo!(),
        };

        let val = self.gen_expression(hir, expr).unwrap();

        self.builder.build_store(ptr, val).unwrap();

        Value::None
    }

    fn gen_if(
        &mut self,
        hir: &ResolvedHir,
        cond: &ResolvedExpression,
        true_branch: &ResolvedExpression,
        false_branch: Option<&ResolvedExpression>,
    ) -> Value<'ctx> {
        let then_block = self
            .context
            .append_basic_block(self.current_function(), "true_branch");

        let end_block = self
            .context
            .append_basic_block(self.current_function(), "end_if");

        let else_block = if false_branch.is_some() {
            let else_block = self
                .context
                .insert_basic_block_after(then_block, "false_branch");
            else_block
        } else {
            end_block
        };

        let cond = self.gen_expression(hir, cond).unwrap().into_int_value();
        self.builder
            .build_conditional_branch(cond, then_block, else_block)
            .unwrap();

        self.builder.position_at_end(then_block);
        let then_value = self.gen_expression(hir, true_branch);
        if !matches!(then_value, Value::Never) {
            self.builder.build_unconditional_branch(end_block).unwrap();
        }

        let else_value = match false_branch {
            None => Value::None,
            Some(false_branch) => {
                self.builder.position_at_end(else_block);

                let value = self.gen_expression(hir, false_branch);

                if !matches!(value, Value::Never) {
                    self.builder.build_unconditional_branch(end_block).unwrap();
                }

                value
            }
        };

        self.builder.position_at_end(end_block);
        match (then_value, else_value) {
            (Value::Some(then_value), Value::Some(else_value)) => {
                let if_value = self
                    .builder
                    .build_phi(then_value.get_type(), "if_result")
                    .unwrap();
                if_value.add_incoming(&[(&then_value, then_block), (&else_value, else_block)]);
                Value::Some(if_value.as_basic_value())
            }
            (Value::Some(then_value), Value::None) | (Value::Some(then_value), Value::Never) => {
                Value::Some(then_value)
            }
            (Value::None, Value::Some(else_value)) | (Value::Never, Value::Some(else_value)) => {
                Value::Some(else_value)
            }
            (Value::None, _) => Value::None,
            (_, Value::None) => Value::None,
            (Value::Never, Value::Never) => {
                self.builder.build_unreachable().unwrap();
                Value::Never
            }
        }
    }

    fn gen_expression_ident(
        &self,
        hir: &ResolvedHir,
        ident_ref: &ResolvedIdentifierRef,
    ) -> BasicValueEnum<'ctx> {
        if self.variables.contains_key(&ident_ref.resolved_symbol_id()) {
            return self
                .builder
                .build_load(
                    self.llvm_type(hir, hir.symbols[ident_ref.resolved_symbol_id()].type_id),
                    self.variables[&ident_ref.resolved_symbol_id()],
                    &format!(
                        "{}#local#sym{}#",
                        &hir.identifiers[ident_ref.ident.id],
                        ident_ref.resolved_symbol_id()
                    ),
                )
                .unwrap();
        };

        match &hir.symbols[ident_ref.resolved_symbol_id()].kind {
            SymbolKind::NotFound => todo!(),
            SymbolKind::Let(_) => unreachable!("handled in the if variable.contains_key(..) above"),
            SymbolKind::LetFn(_, _, _) => todo!(),
            SymbolKind::Parameter(_, index) => self
                .current_function()
                .get_nth_param(*index as u32)
                .unwrap(),
            SymbolKind::Struct(_) => todo!(),
            SymbolKind::Field(_, _) => todo!(),
            SymbolKind::NativeType(_, _) => todo!(),
            SymbolKind::Native(_, _, _, _) => todo!(),
        }
    }

    fn gen_function_call(
        &mut self,
        hir: &ResolvedHir,
        ident_ref: &ResolvedIdentifierRef,
        params: &[ExprId],
    ) -> Value<'ctx> {
        let symbol = &hir.symbols[hir.identifier_refs[ident_ref.id].resolved_symbol_id()];
        if let SymbolKind::Native(_, _, _, kind) = &symbol.kind {
            if kind.is_instr() {
                return kind.gen_instr(hir, self, params);
            }
        }

        let parameters = params
            .iter()
            .map(|e| match self.gen_expression(hir, &hir.expressions[*e]) {
                Value::None | Value::Never => panic!(),
                Value::Some(BasicValueEnum::ArrayValue(_)) => todo!(),
                Value::Some(BasicValueEnum::IntValue(val)) => BasicMetadataValueEnum::IntValue(val),
                Value::Some(BasicValueEnum::FloatValue(_)) => todo!(),
                Value::Some(BasicValueEnum::PointerValue(_)) => todo!(),
                Value::Some(BasicValueEnum::StructValue(_)) => todo!(),
                Value::Some(BasicValueEnum::VectorValue(_)) => todo!(),
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
                &format!("{function_name}#res#",),
            )
            .unwrap()
            .try_as_basic_value()
            .left()
            .into()
    }

    fn gen_while(
        &mut self,
        hir: &ResolvedHir,
        cond: &ResolvedExpression,
        body: &ResolvedExpression,
    ) -> Value<'ctx> {
        let cond_block = self
            .context
            .append_basic_block(self.current_function(), "cond");
        let body_block = self
            .context
            .append_basic_block(self.current_function(), "body");
        let end_block = self
            .context
            .append_basic_block(self.current_function(), "end_while");

        self.builder.build_unconditional_branch(cond_block).unwrap();

        self.builder.position_at_end(cond_block);
        let cond = self.gen_expression(hir, cond).unwrap().into_int_value();
        self.builder
            .build_conditional_branch(cond, body_block, end_block)
            .unwrap();

        self.builder.position_at_end(body_block);
        let value = self.gen_expression(hir, body);
        if !matches!(value, Value::Never) {
            self.builder.build_unconditional_branch(cond_block).unwrap();
        }

        self.builder.position_at_end(end_block);
        if matches!(value, Value::Never) {
            self.builder.build_unreachable().unwrap();
        }

        value
    }

    fn current_function(&self) -> FunctionValue<'ctx> {
        self.builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap()
    }

    fn llvm_type(&self, hir: &ResolvedHir, type_id: TypeId) -> BasicTypeEnum<'ctx> {
        match &hir.types[type_id] {
            Type::Invalid => unreachable!(),
            Type::Boolean => self.bool_type.as_basic_type_enum(),
            Type::Function(_, _) => todo!(),
            Type::Struct(_) => todo!(),
            Type::Number => self.i64_type.as_basic_type_enum(),
            Type::Void => unreachable!(),
            Type::None => todo!(),
        }
    }

    /// Generates an `alloca` instruction, optionally storing a value inside, if provided.
    fn gen_alloca(
        &mut self,
        t: BasicTypeEnum<'ctx>,
        identifier: &str,
        symbol_id: SymbolId,
        val: Option<BasicValueEnum<'ctx>>,
    ) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let entry_block = self.current_function().get_first_basic_block().unwrap();
        match entry_block.get_first_instruction() {
            None => builder.position_at_end(entry_block),
            Some(first_instruction) => builder.position_before(&first_instruction),
        };

        let ptr = builder.build_alloca(t, identifier).unwrap();

        if let Some(val) = val {
            builder.build_store(ptr, val).unwrap();
        }

        self.variables.insert(symbol_id, ptr);

        ptr
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value<'ctx> {
    Never,
    None,
    Some(BasicValueEnum<'ctx>),
}

impl<'ctx> Value<'ctx> {
    fn unwrap(self) -> BasicValueEnum<'ctx> {
        match self {
            Value::Never | Value::None => panic!(),
            Value::Some(val) => val,
        }
    }
}

impl<'ctx> From<Option<BasicValueEnum<'ctx>>> for Value<'ctx> {
    fn from(value: Option<BasicValueEnum<'ctx>>) -> Self {
        match value {
            None => Value::None,
            Some(val) => Value::Some(val),
        }
    }
}

trait LlvmImpl {
    fn is_instr(&self) -> bool;

    fn gen_instr<'ctx>(
        &self,
        hir: &ResolvedHir,
        codegen: &mut Codegen<'ctx, '_>,
        params: &[ExprId],
    ) -> Value<'ctx>;
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
        codegen: &mut Codegen<'ctx, '_>,
        params: &[ExprId],
    ) -> Value<'ctx> {
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_add(lhs, rhs, "add#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_sub(lhs, rhs, "sub#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_mul(lhs, rhs, "mul#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_signed_div(lhs, rhs, "div#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ne#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SGE, lhs, rhs, "ge#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::SLE, lhs, rhs, "le#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq#")
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
                Value::Some(
                    codegen
                        .builder
                        .build_int_compare(IntPredicate::NE, lhs, rhs, "ne#")
                        .unwrap()
                        .into(),
                )
            }
            NativeFnKind::PrintNumber => Value::None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Codegen;
    use inkwell::context::Context;
    use inkwell::targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine};
    use inkwell::OptimizationLevel;
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

                Target::initialize_all(&InitializationConfig::default());

                let target_triple = TargetMachine::get_default_triple();
                let target = Target::from_triple(&target_triple).unwrap();
                let target_machine = target
                    .create_target_machine(
                        &target_triple,
                        "generic",
                        "",
                        OptimizationLevel::None,
                        RelocMode::PIC,
                        CodeModel::Default,
                    )
                    .unwrap();

                let context = Context::create();
                let codegen = Codegen::new(&context, &target_triple, &target_machine);
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

    gen!(
        assign_parameter,
        r#"
        let f(n: number): number = {
            n = n + 1;
            ret n;
        }
        "#
    );
    gen!(
        assign_local,
        r#"
        let f(n: number): number = {
            let m = n;
            m = m + 1;
            ret m;
        }
        "#
    );

    gen!(
        fibo_rec,
        r#"
        let f(n: number): number = {
            if n <= 1 {
                ret n;
            }
            f(n - 1) + f(n - 2);
        }
        "#
    );
    gen!(
        fibo_iter,
        r#"
        let f(n: number): number = {
            if n == 0 { ret 0; }
            if n == 1 { ret 1; }

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

    gen!(
        let_produces_alloca_at_entry,
        r#"
        let f(n: number): number = {
            if n == 42 {
                let m = 0;
                ret m + 1;
            } else {
                let m = 0;
                ret m - 1;
            };
        }
        "#
    );

    gen!(
        if_simple,
        r#"
        let f() = {
            if true {
            } else {
            };
        }
        "#
    );
    gen!(
        if_then_else_value,
        r#"
        let f(n: number, c: boolean): boolean = {
            let m = if c {
                n - 1;
            } else {
                n + 1;
            };
            ret m == 42;
        }
        "#
    );
    gen!(
        if_then_value,
        r#"
        let f(n: number): boolean = {
            let m = if n != 42 {
                n - 1;
            } else {
                ret true;
            };
            ret m == 42;
        }
        "#
    );
    gen!(
        if_else_value,
        r#"
        let f(n: number): boolean = {
            let m = if n == 42 {
                ret true;
            } else {
                n - 1;
            };
            ret m == 42;
        }
        "#
    );

    gen!(
        while_simple,
        r#"
        let f(n: number) = {
            while true {
            }
        }
        "#
    );
    gen!(
        while_no_ret,
        r#"
        let f(n: number): boolean = {
            while n < 42 {
                n + 1;
            }
            ret true;
        }
        "#
    );
    gen!(
        while_ret,
        r#"
        let f(n: number): number = {
            while n != 42 {
                ret n;
            }
            ret 42;
        }
        "#
    );
    gen!(
        while_value,
        r#"
        let f(n: number): number = {
            while n < 42 {
                n = n + 1;
            }
            ret n;
        }
        "#
    );
}
