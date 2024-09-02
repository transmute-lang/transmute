use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::types::{
    BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, StructType, VoidType,
};
use inkwell::values::{
    AggregateValue, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, PointerValue,
};
use inkwell::{IntPredicate, OptimizationLevel};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use transmute_core::error::Diagnostics;
use transmute_core::ids::{ExprId, StructId, SymbolId, TypeId};
use transmute_mir::{
    Expression, ExpressionKind, Function, Mir, Statement, StatementKind, Struct, Type,
};
use transmute_mir::{LiteralKind, SymbolKind, Target as AssignmentTarget};
use transmute_mir::{NativeFnKind, Variable};

// todo add support for void functions
// todo add support for structs nested in functions (does not work because of resolver)
// todo add support for nested structs

pub struct LlvmIrGen {
    context: Context,
    target_triple: TargetTriple,
    optimize: bool,
}

impl LlvmIrGen {
    pub fn gen(&self, mir: &Mir) -> Result<LlvmIr, Diagnostics> {
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
            .gen(mir, self.optimize)
            .map(|module| LlvmIr {
                module,
                target_machine,
            })
    }

    pub fn set_optimize(&mut self, optimize: bool) {
        self.optimize = optimize;
    }
}

impl Default for LlvmIrGen {
    fn default() -> Self {
        Self {
            context: Context::create(),
            target_triple: TargetMachine::get_default_triple(),
            optimize: false,
        }
    }
}

pub struct LlvmIr<'ctx> {
    module: Module<'ctx>,
    target_machine: TargetMachine,
}

impl<'ctx> LlvmIr<'ctx> {
    // todo error handling
    pub fn build_bin<P: Into<PathBuf>>(&self, crt: &[u8], path: P) -> Result<(), Diagnostics> {
        let path = path.into();

        let tm_object_path = path.clone().with_extension("o");
        self.target_machine
            .write_to_file(&self.module, FileType::Object, &tm_object_path)
            .unwrap();

        let crt_object_path = path.with_file_name("crt.o");
        let crt_module = self
            .module
            .get_context()
            .create_module_from_ir(MemoryBuffer::create_from_memory_range(crt, "crt"))
            .unwrap();
        self.target_machine
            .write_to_file(&crt_module, FileType::Object, &crt_object_path)
            .unwrap();

        match Command::new("cc")
            .arg(&tm_object_path)
            .arg(&crt_object_path)
            .arg("-o")
            .arg(&path)
            .output()
        {
            Ok(_) => {
                println!("Wrote executable to {}", path.display());
            }
            Err(err) => {
                eprintln!("{err}");
            }
        }

        fs::remove_file(crt_object_path).unwrap();
        fs::remove_file(tm_object_path).unwrap();

        Ok(())
    }

    pub fn write_ir<P: AsRef<Path>>(&self, path: P) -> Result<(), Diagnostics> {
        let str = self.module.to_string();
        fs::write(path, &str).unwrap();
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

    struct_types: HashMap<StructId, StructType<'ctx>>,
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
            struct_types: HashMap::default(),
            variables: HashMap::default(),
            target_triple,
            target_machine,
        }
    }

    pub fn gen(mut self, mir: &Mir, optimize: bool) -> Result<Module<'ctx>, Diagnostics> {
        for (struct_id, struct_def) in mir.structs.iter() {
            self.gen_struct_signature(mir, struct_id, struct_def);
        }
        for (struct_id, struct_def) in mir.structs.iter() {
            self.gen_struct_body(mir, struct_id, struct_def);
        }

        for (_, function) in mir.functions.iter() {
            self.gen_function_signature(mir, function);
        }
        for (_, function) in mir.functions.iter() {
            self.gen_function_body(mir, function);
        }

        self.module.verify().unwrap_or_else(|str| {
            #[cfg(debug_assertions)]
            eprintln!("{}", self.module.to_string());
            panic!("Invalid LLVM IR generated:\n{}", str.to_string());
        });

        if optimize {
            self.optimize();
        }

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

    fn gen_statement(&mut self, mir: &Mir, stmt: &Statement) -> Value<'ctx> {
        match &stmt.kind {
            StatementKind::Expression(expr_id) => {
                self.gen_expression(mir, &mir.expressions[*expr_id])
            }
            StatementKind::Ret(expr_id) => self.gen_ret(mir, &mir.expressions[*expr_id]),
        }
    }

    fn gen_ret(&mut self, mir: &Mir, expr: &Expression) -> Value<'ctx> {
        match self.gen_expression(mir, expr) {
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

    fn gen_struct_signature(&mut self, mir: &Mir, struct_id: StructId, struct_def: &Struct) {
        let struct_type = self.context.opaque_struct_type(&format!(
            "{}#id{}",
            &mir.identifiers[struct_def.identifier.id], struct_id
        ));
        self.struct_types.insert(struct_id, struct_type);
    }

    fn gen_struct_body(&mut self, mir: &Mir, struct_id: StructId, struct_def: &Struct) {
        let fields = struct_def
            .fields
            .iter()
            .map(|field| self.llvm_type(mir, field.type_id))
            .collect::<Vec<BasicTypeEnum>>();

        let struct_type = *self.struct_types.get(&struct_id).unwrap();

        struct_type.set_body(fields.as_slice(), false);
    }

    fn gen_function_signature(&mut self, mir: &Mir, function: &Function) {
        let parameters_types = function
            .parameters
            .iter()
            .map(|param| self.llvm_type(mir, param.type_id).into())
            .collect::<Vec<BasicMetadataTypeEnum>>();

        let resolved_ret_type = &mir.types[function.ret];
        let fn_type = match resolved_ret_type {
            Type::Boolean => self.bool_type.fn_type(&parameters_types, false),
            Type::Function(_, _) => todo!(),
            Type::Struct(_, _) => todo!(),
            Type::Number => self.i64_type.fn_type(&parameters_types, false),
            Type::Void => self.void_type.fn_type(&parameters_types, false),
            Type::None => todo!(),
        };

        self.module
            .add_function(&mir.identifiers[function.identifier.id], fn_type, None);
    }

    fn gen_function_body(&mut self, mir: &Mir, function: &Function) -> Value<'ctx> {
        // It is ok for now to get a function by name, but this might need to change when we start
        // to mangle function names. When we do it, gen_function_signature() can return the function
        // value that we can reuse here.
        let llvm_function = self
            .module
            .get_function(&mir.identifiers[function.identifier.id])
            .unwrap();

        let entry = self.context.append_basic_block(llvm_function, "entry");
        self.builder.position_at_end(entry);

        for (i, param) in llvm_function.get_param_iter().enumerate() {
            let name = format!(
                "{}#param#sym{}#",
                &mir.identifiers[function.parameters[i].identifier.id],
                function.parameters[i].symbol_id
            );
            match param {
                BasicValueEnum::ArrayValue(_) => todo!(),
                BasicValueEnum::IntValue(val) => val.set_name(&name),
                BasicValueEnum::FloatValue(_) => todo!(),
                BasicValueEnum::PointerValue(_) => todo!(),
                BasicValueEnum::StructValue(_) => todo!(),
                BasicValueEnum::VectorValue(_) => todo!(),
            }

            if function.parameters[i].mutable {
                self.gen_alloca(
                    param.get_type(),
                    &format!(
                        "{}#local#sym{}#",
                        &mir.identifiers[function.parameters[i].identifier.id],
                        function.parameters[i].symbol_id
                    ),
                    function.parameters[i].symbol_id,
                    Some(param),
                );
            }
        }

        for (_, variable) in function.variables.iter() {
            self.gen_variable(mir, variable);
        }

        self.gen_expression(mir, &mir.expressions[function.body]);

        Value::None
    }

    fn gen_variable(&mut self, mir: &Mir, variable: &Variable) {
        let llvm_type = self.llvm_type(mir, variable.type_id);

        self.gen_alloca(
            llvm_type,
            &format!(
                "{}#local#sym{}#",
                &mir.identifiers[variable.identifier.id], variable.symbol_id
            ),
            variable.symbol_id,
            None,
        );
    }

    fn gen_expression(&mut self, mir: &Mir, expr: &Expression) -> Value<'ctx> {
        let value = match &expr.kind {
            ExpressionKind::Assignment(target, expr) => {
                self.gen_assignment(mir, target, &mir.expressions[*expr])
            }
            ExpressionKind::If(cond_expr_id, true_expr_id, false_expr_id) => self.gen_if(
                mir,
                &mir.expressions[*cond_expr_id],
                &mir.expressions[*true_expr_id],
                false_expr_id.map(|expr_id| &mir.expressions[expr_id]),
            ),
            ExpressionKind::Literal(literal) => match &literal.kind {
                LiteralKind::Boolean(bool) => {
                    Value::Some(self.bool_type.const_int(*bool as u64, false).into())
                }
                LiteralKind::Identifier(symbol_id) => {
                    Value::Some(self.gen_expression_ident(mir, *symbol_id))
                }
                LiteralKind::Number(number) => {
                    // todo check what happens for negative numbers
                    Value::Some(self.i64_type.const_int(*number as u64, false).into())
                }
            },
            ExpressionKind::Access(expr_id, symbol_id) => {
                self.gen_access(mir, *expr_id, *symbol_id)
            }
            ExpressionKind::FunctionCall(symbol_id, params) => {
                self.gen_function_call(mir, *symbol_id, params)
            }
            ExpressionKind::While(cond, body) => {
                self.gen_while(mir, &mir.expressions[*cond], &mir.expressions[*body])
            }
            ExpressionKind::Block(stmt_ids) => {
                let mut value = Value::None;
                for stmt_id in stmt_ids {
                    value = self.gen_statement(mir, &mir.statements[*stmt_id]);
                    if matches!(value, Value::Never) {
                        return value;
                    }
                }
                value
            }
            ExpressionKind::StructInstantiation(_, struct_id, fields) => {
                self.gen_struct_instantiation(mir, *struct_id, fields)
            }
        };

        #[cfg(debug_assertions)]
        {
            let t = &mir.types[expr.type_id];
            debug_assert!(
                t != &Type::None && value != Value::Never
                    || t == &Type::None && value == Value::Never
            );
        }

        value
    }

    fn gen_assignment(
        &mut self,
        mir: &Mir,
        target: &AssignmentTarget,
        expr: &Expression,
    ) -> Value<'ctx> {
        let value = self.gen_expression(mir, expr).unwrap();

        match target {
            AssignmentTarget::Direct(symbol_id) => {
                self.builder
                    .build_store(self.variables[symbol_id], value)
                    .unwrap();
            }
            AssignmentTarget::Indirect(expr_id) => {
                let (target, _) = self.gen_pointer_expression(mir, &mir.expressions[*expr_id]);
                self.builder.build_store(target, value).unwrap();
            }
        }

        Value::None
    }

    fn gen_pointer_expression(
        &mut self,
        mir: &Mir,
        expression: &Expression,
    ) -> (PointerValue<'ctx>, BasicTypeEnum<'ctx>) {
        match &expression.kind {
            ExpressionKind::Literal(literal) => match &literal.kind {
                LiteralKind::Identifier(symbol_id) => {
                    let struct_pointer = *self.variables.get(symbol_id).unwrap();
                    let struct_type = self.llvm_type(mir, mir.symbols[*symbol_id].type_id);
                    (struct_pointer, struct_type)
                }
                LiteralKind::Boolean(_) => panic!("a boolean is not a pointer"),
                LiteralKind::Number(_) => panic!("a number is not a pointer"),
            },
            ExpressionKind::Access(expr_id, symbol_id) => {
                let (struct_ptr, struct_type) =
                    self.gen_pointer_expression(mir, &mir.expressions[*expr_id]);

                let symbol = &mir.symbols[*symbol_id];
                let (ident_id, index) = match symbol.kind {
                    SymbolKind::Field(_, ident_id, index) => (ident_id, index),
                    _ => panic!("only fields can be accessed"),
                };

                let name = format!(
                    "{}.{}#idx{}#sym{}#",
                    struct_ptr.get_name().to_str().unwrap(),
                    mir.identifiers[ident_id],
                    index,
                    symbol_id
                );
                let target_ptr = self
                    .builder
                    .build_struct_gep(struct_type, struct_ptr, index as u32, &name)
                    .unwrap();

                (target_ptr, self.llvm_type(mir, symbol.type_id))
            }
            _ => panic!(),
        }
    }

    fn gen_if(
        &mut self,
        mir: &Mir,
        cond: &Expression,
        true_branch: &Expression,
        false_branch: Option<&Expression>,
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

        let cond = self.gen_expression(mir, cond).unwrap().into_int_value();
        self.builder
            .build_conditional_branch(cond, then_block, else_block)
            .unwrap();

        self.builder.position_at_end(then_block);
        let then_value = self.gen_expression(mir, true_branch);
        if !matches!(then_value, Value::Never) {
            self.builder.build_unconditional_branch(end_block).unwrap();
        }

        let else_value = match false_branch {
            None => Value::None,
            Some(false_branch) => {
                self.builder.position_at_end(else_block);

                let value = self.gen_expression(mir, false_branch);

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

    fn gen_expression_ident(&self, mir: &Mir, symbol_id: SymbolId) -> BasicValueEnum<'ctx> {
        if self.variables.contains_key(&symbol_id) {
            return self
                .builder
                .build_load(
                    self.llvm_type(mir, mir.symbols[symbol_id].type_id),
                    self.variables[&symbol_id],
                    &format!(
                        "{}#local#sym{}#",
                        mir.identifiers[mir.symbols[symbol_id].ident_id], symbol_id
                    ),
                )
                .unwrap();
        };

        match &mir.symbols[symbol_id].kind {
            SymbolKind::Let(_) => {
                unreachable!("handled in the if variable.contains_key(..) above")
            }
            SymbolKind::LetFn(_, _, _) => todo!(),
            SymbolKind::Parameter(_, index) => self
                .current_function()
                .get_nth_param(*index as u32)
                .unwrap(),
            SymbolKind::Struct(_) => todo!(),
            SymbolKind::Field(_, _, _) => todo!(),
            SymbolKind::NativeType(_, _) => todo!(),
            SymbolKind::Native(_, _, _, _) => todo!(),
        }
    }

    fn gen_access(&mut self, mir: &Mir, expr_id: ExprId, symbol_id: SymbolId) -> Value<'ctx> {
        let (ident_id, index) = match &mir.symbols[symbol_id].kind {
            SymbolKind::Field(_, ident_id, index) => (*ident_id, *index),
            _ => panic!("invalid symbol type"),
        };

        let value = match self.gen_expression(mir, &mir.expressions[expr_id]).unwrap() {
            BasicValueEnum::ArrayValue(_) => todo!(),
            BasicValueEnum::StructValue(v) => v,
            _ => panic!("invalid value type"),
        };

        let name = format!(
            "{}.{}#idx{}#sym{}#",
            value.get_name().to_str().unwrap(),
            &mir.identifiers[ident_id],
            index,
            symbol_id
        );

        // todo see if we can replace with GEP+load (as for struct instantiation)
        Value::Some(
            self.builder
                .build_extract_value(value, index as u32, &name)
                .unwrap(),
        )
    }

    fn gen_function_call(
        &mut self,
        mir: &Mir,
        symbol_id: SymbolId,
        params: &[ExprId],
    ) -> Value<'ctx> {
        let symbol = &mir.symbols[symbol_id];
        if let SymbolKind::Native(_, _, _, kind) = &symbol.kind {
            if kind.is_instr() {
                return kind.gen_instr(mir, self, params);
            }
        }

        let parameters = params
            .iter()
            .map(|e| match self.gen_expression(mir, &mir.expressions[*e]) {
                Value::None | Value::Never => panic!(),
                Value::Some(BasicValueEnum::ArrayValue(_)) => todo!(),
                Value::Some(BasicValueEnum::IntValue(val)) => BasicMetadataValueEnum::IntValue(val),
                Value::Some(BasicValueEnum::FloatValue(_)) => todo!(),
                Value::Some(BasicValueEnum::PointerValue(_)) => todo!(),
                Value::Some(BasicValueEnum::StructValue(_)) => todo!(),
                Value::Some(BasicValueEnum::VectorValue(_)) => todo!(),
            })
            .collect::<Vec<BasicMetadataValueEnum>>();

        let function_name = &mir.identifiers[mir.symbols[symbol_id].ident_id];

        let called_function = self
            .module
            .get_function(function_name)
            .unwrap_or_else(|| panic!("called function `{}` not defined", function_name));
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

    fn gen_while(&mut self, mir: &Mir, cond: &Expression, body: &Expression) -> Value<'ctx> {
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
        let cond = self.gen_expression(mir, cond).unwrap().into_int_value();
        self.builder
            .build_conditional_branch(cond, body_block, end_block)
            .unwrap();

        self.builder.position_at_end(body_block);
        let value = self.gen_expression(mir, body);
        if !matches!(value, Value::Never) {
            self.builder.build_unconditional_branch(cond_block).unwrap();
        }

        self.builder.position_at_end(end_block);
        if matches!(value, Value::Never) {
            self.builder.build_unreachable().unwrap();
        }

        value
    }

    fn gen_struct_instantiation(
        &mut self,
        mir: &Mir,
        struct_id: StructId,
        fields: &[(SymbolId, ExprId)],
    ) -> Value<'ctx> {
        let field_values = fields
            .iter()
            .map(
                |(_, expr_id)| match self.gen_expression(mir, &mir.expressions[*expr_id]) {
                    Value::Some(val) => val,
                    _ => panic!("value expected"),
                },
            )
            .collect::<Vec<BasicValueEnum>>();

        let const_values = field_values
            .iter()
            .map(|value| {
                if Self::is_const(value) {
                    *value
                } else {
                    Self::get_undef(&value.get_type())
                }
            })
            .collect::<Vec<BasicValueEnum>>();

        // todo review whether it makes sense to use GEP+store instead of insertvalue
        //  ref: https://stackoverflow.com/questions/35234940/llvm-gep-and-store-vs-load-and-insertvalue-storing-value-to-a-pointer-to-an-agg
        let struct_type = *self.struct_types.get(&struct_id).unwrap();
        let mut struct_value = struct_type
            .const_named_struct(&const_values)
            .as_aggregate_value_enum();

        for (index, value) in field_values.into_iter().enumerate() {
            if !Self::is_const(&value) {
                struct_value = self
                    .builder
                    .build_insert_value(struct_value, value, index as u32, "insert")
                    .unwrap();
            }
        }

        Value::Some(struct_value.as_basic_value_enum())
    }

    fn current_function(&self) -> FunctionValue<'ctx> {
        self.builder
            .get_insert_block()
            .unwrap()
            .get_parent()
            .unwrap()
    }

    fn llvm_type(&self, mir: &Mir, type_id: TypeId) -> BasicTypeEnum<'ctx> {
        match &mir.types[type_id] {
            Type::Boolean => self.bool_type.as_basic_type_enum(),
            Type::Function(_, _) => todo!(),
            Type::Struct(_, struct_id) => {
                BasicTypeEnum::StructType(*self.struct_types.get(struct_id).unwrap())
            }
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

    fn is_const(value: &BasicValueEnum<'ctx>) -> bool {
        match value {
            BasicValueEnum::ArrayValue(val) => val.is_const(),
            BasicValueEnum::FloatValue(val) => val.is_const(),
            BasicValueEnum::IntValue(val) => val.is_const(),
            BasicValueEnum::PointerValue(val) => val.is_const(),
            BasicValueEnum::StructValue(_) => false,
            BasicValueEnum::VectorValue(val) => val.is_const(),
        }
    }

    fn get_undef(typ: &BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
        match typ {
            BasicTypeEnum::ArrayType(ty) => ty.get_undef().into(),
            BasicTypeEnum::FloatType(ty) => ty.get_undef().into(),
            BasicTypeEnum::IntType(ty) => ty.get_undef().into(),
            BasicTypeEnum::PointerType(ty) => ty.get_undef().into(),
            BasicTypeEnum::StructType(ty) => ty.get_undef().into(),
            BasicTypeEnum::VectorType(ty) => ty.get_undef().into(),
        }
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
        mir: &Mir,
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
        mir: &Mir,
        codegen: &mut Codegen<'ctx, '_>,
        params: &[ExprId],
    ) -> Value<'ctx> {
        match self {
            NativeFnKind::NegNumber => todo!(),
            NativeFnKind::AddNumberNumber => {
                let lhs = codegen
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
                    .gen_expression(mir, &mir.expressions[params[0]])
                    .unwrap()
                    .into_int_value();
                let rhs = codegen
                    .gen_expression(mir, &mir.expressions[params[1]])
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
    use transmute_mir::make_mir;

    macro_rules! gen {
        ($name:ident, $src:expr) => {
            paste::paste! {
                #[test]
                fn [< $name _unoptimized >]() {
                    let ast = Parser::new(Lexer::new($src)).parse().unwrap();
                    let hir = UnresolvedHir::from(ast).resolve(Natives::new()).unwrap();
                    let mir = make_mir(hir).unwrap();

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
                    let llvm_ir = codegen
                    .gen(&mir, false)
                    .unwrap()
                    .to_string();
                    assert_snapshot!(llvm_ir);
                }

                #[test]
                fn [< $name _optimized >]() {
                    let ast = Parser::new(Lexer::new($src)).parse().unwrap();
                    let hir = UnresolvedHir::from(ast).resolve(Natives::new()).unwrap();
                    let mir = make_mir(hir).unwrap();

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
                    let llvm_ir = codegen
                    .gen(&mir, true)
                    .unwrap()
                    .to_string();
                    assert_snapshot!(llvm_ir);
                }
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

    gen!(
        nested_function,
        r#"
        let f(): number {
            let g(): number {
                1;
            };
            g();
        }
        "#
    );

    gen!(
        struct_instantiate_1_const_field,
        r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct { field: 1 };
            1;
        }
        "#
    );

    gen!(
        struct_instantiate_2_const_field,
        r#"
        struct Struct { field1: number, field2: boolean }
        let f(): number {
            let s = Struct { field2: true, field1: 1 };
            1;
        }
        "#
    );

    gen!(
        struct_instantiate_1_field_var,
        r#"
        struct Struct { field: number }
        let f(n: number): number {
            let s = Struct {
                field: n + 1,
            };
            1;
        }
        "#
    );

    gen!(
        struct_instantiate_2_fields_var,
        r#"
        struct Struct { field1: number, field2: number }
        let f(n: number): number {
            let s = Struct {
                field2: n + 2,
                field1: n + 1,
            };
            1;
        }
        "#
    );

    gen!(
        struct_instantiate_2_fields_mixed1,
        r#"
        struct Struct { field1: number, field2: number }
        let f(n: number): number {
            let s = Struct {
                field1: n + 1,
                field2: 0,
            };
            1;
        }
        "#
    );

    gen!(
        struct_instantiate_2_fields_mixed2,
        r#"
        struct Struct { field1: number, field2: number }
        let f(n: number): number {
            let s = Struct {
                field1: 0,
                field2: n + 1,
            };
            1;
        }
        "#
    );

    gen!(
        struct_read_field,
        r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct {
                field: 1
            };

            s.field;
        }
        "#
    );

    gen!(
        struct_write_field_const,
        r#"
        struct Struct { field: number }
        let f(): number {
            let s = Struct {
                field: 1
            };

            s.field = 2;

            1;
        }
        "#
    );

    gen!(
        struct_declared_out_of_order,
        r#"
        struct StructOuter { inner: StructInner }
        struct StructInner {  }
        let f(): number {
            let outer = StructOuter {
                inner: StructInner {  }
            };
            1;
        }
        "#
    );
}
