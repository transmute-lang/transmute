mod mangling;

use crate::mangling::mangle;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::memory_buffer::MemoryBuffer;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::types::{
    BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, PointerType, StructType, VoidType,
};
use inkwell::values::{
    BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue,
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

// fixme add support for structs nested in functions (does not work because of resolver)
// todo:refactoring refactor struct layout so we dont need a `_glob` function. we can do it on the
//   fly, the first time a struct is instantiated

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
    // todo:ux error handling
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
            Ok(o) => {
                if !o.status.success() {
                    println!("{:?}", o);
                }
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

    pub fn write_assembly<P: AsRef<Path>>(&self, path: P) -> Result<(), Diagnostics> {
        self.target_machine
            .write_to_file(&self.module, FileType::Assembly, path.as_ref())
            .unwrap();
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
    ptr_type: PointerType<'ctx>,

    llvm_gcroot: FunctionValue<'ctx>,
    malloc: FunctionValue<'ctx>,
    #[cfg(any(test, feature = "gc-aggressive"))]
    gc_run: FunctionValue<'ctx>,

    struct_types: HashMap<StructId, StructType<'ctx>>,
    type_layouts: HashMap<TypeId, PointerValue<'ctx>>,
    variables: HashMap<SymbolId, PointerValue<'ctx>>,
    functions: HashMap<SymbolId, FunctionValue<'ctx>>,

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
        let size_type = context.i64_type();
        let void_type = context.void_type();
        let ptr_type = context.ptr_type(Default::default());

        Self {
            context,
            builder,
            bool_type,
            i64_type,
            void_type,
            ptr_type,
            llvm_gcroot: {
                let llvm_gcroot_fn_type =
                    void_type.fn_type(&[ptr_type.into(), ptr_type.into()], false);
                module.add_function("llvm.gcroot", llvm_gcroot_fn_type, None)
            },
            malloc: {
                let malloc_fn_type = ptr_type.fn_type(&[size_type.into()], false);
                module.add_function("gc_malloc", malloc_fn_type, None)
            },
            #[cfg(any(test, feature = "gc-aggressive"))]
            gc_run: {
                let gc_fn_type = void_type.fn_type(&[], false);
                module.add_function("gc_run", gc_fn_type, None)
            },
            struct_types: Default::default(),
            type_layouts: Default::default(),
            variables: Default::default(),
            functions: Default::default(),
            target_triple,
            target_machine,
            module,
        }
    }

    pub fn gen(mut self, mir: &Mir, optimize: bool) -> Result<Module<'ctx>, Diagnostics> {
        for (symbol_id, symbol) in mir.symbols.iter() {
            if let SymbolKind::Native(ident_id, parameters, _, native_kind) = &symbol.kind {
                let fn_name = mangle(mir, *ident_id, parameters);
                match native_kind {
                    NativeFnKind::PrintNumber => {
                        let print_fn_type = self.void_type.fn_type(&[self.i64_type.into()], false);
                        let print_fn = self.module.add_function(&fn_name, print_fn_type, None);
                        self.functions.insert(symbol_id, print_fn);
                    }
                    NativeFnKind::PrintBoolean => {
                        let print_fn_type = self.void_type.fn_type(&[self.bool_type.into()], false);
                        let print_fn = self.module.add_function(&fn_name, print_fn_type, None);
                        self.functions.insert(symbol_id, print_fn);
                    }
                    _ => {
                        // nothing to do
                    }
                }
            }
        }

        for (struct_id, struct_def) in mir.structs.iter() {
            self.gen_struct_signature(mir, struct_id, struct_def);
        }
        for (struct_id, struct_def) in mir.structs.iter() {
            self.gen_struct_body(mir, struct_id, struct_def);
        }

        let f = self.module.add_function(
            "_glob",
            self.void_type.fn_type(&[], false),
            Some(Linkage::Private),
        );
        let block = self.context.append_basic_block(f, "entry");
        self.builder.position_at_end(block);
        for (struct_id, _) in mir.structs.iter() {
            self.gen_struct_layout(mir, struct_id);
        }
        self.builder.build_unreachable().unwrap();

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
            // "instcombine", // fixme why doesn't this work?
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
            .map(|field| self.repr(self.llvm_type(mir, field.type_id)))
            .collect::<Vec<BasicTypeEnum>>();

        let struct_type = *self.struct_types.get(&struct_id).unwrap();

        struct_type.set_body(fields.as_slice(), false);

        let offsets_count = struct_type
            .get_field_types_iter()
            .filter(|f| matches!(f, BasicTypeEnum::PointerType(_)))
            .count();

        // todo:refactoring find a way to make it using structs instead of a flat array of i64
        let i64_array_type = self.i64_type.array_type(offsets_count as u32 * 2 + 1);
        let global = self.module.add_global(
            i64_array_type,
            None,
            &format!(
                "layout_struct_{}",
                mir.identifiers[mir.structs[struct_id].identifier.id]
            ),
        );
        // global.set_constant(true);
        // global.set_externally_initialized(false);
        // global.set_linkage(Linkage::LinkerPrivate);

        self.type_layouts.insert(
            mir.symbols[mir.structs[struct_id].symbol_id].type_id,
            global.as_pointer_value(),
        );
    }

    /// the struct layout is an array of i64.
    /// the first one gives the count of pointer fields, n
    /// then, n pairs of i64 follows:
    ///  - the first element is the field's offset
    ///  - the second element is the field's layout pointer
    fn gen_struct_layout(&mut self, mir: &Mir, struct_id: StructId) {
        let global = self
            .module
            .get_global(&format!(
                "layout_struct_{}",
                mir.identifiers[mir.structs[struct_id].identifier.id]
            ))
            .unwrap();

        debug_assert!(global.get_value_type().into_array_type().len() % 2 == 1);

        let mut offsets =
            Vec::with_capacity(global.get_value_type().into_array_type().len() as usize);
        let entries_count = (global.get_value_type().into_array_type().len() - 1) / 2;
        offsets.push(self.i64_type.const_int(entries_count as u64, false));

        let struct_type = self.struct_types[&struct_id];
        for field in mir.structs[struct_id].fields.iter() {
            if let Some(field_layout_ptr) = self.type_layouts.get(&field.type_id) {
                let field_pointer = self
                    .builder
                    .build_struct_gep(
                        struct_type,
                        self.ptr_type.const_null(),
                        field.index as u32,
                        &format!("offset_struct{struct_id}_field{index}", index = field.index),
                    )
                    .unwrap();
                let field_offset = self
                    .builder
                    .build_ptr_to_int(
                        field_pointer,
                        self.i64_type,
                        &format!("offset_struct{struct_id}_field{index}", index = field.index),
                    )
                    .unwrap();
                offsets.push(field_offset);

                let field_layout_ptr = self
                    .builder
                    .build_ptr_to_int(
                        *field_layout_ptr,
                        self.i64_type,
                        &format!("offset_struct{struct_id}_field{index}", index = field.index),
                    )
                    .unwrap();
                offsets.push(field_layout_ptr);
            }
        }

        global.set_initializer(&self.i64_type.const_array(&offsets));
    }

    fn gen_function_signature(&mut self, mir: &Mir, function: &Function) {
        let parameters_types = function
            .parameters
            .iter()
            .map(|param| {
                let parameter_type = self.llvm_type(mir, param.type_id);
                match parameter_type {
                    BasicTypeEnum::ArrayType(_) => todo!(),
                    BasicTypeEnum::FloatType(_) => parameter_type.into(),
                    BasicTypeEnum::IntType(_) => parameter_type.into(),
                    BasicTypeEnum::PointerType(_) => unimplemented!("pointers are not supported"),
                    BasicTypeEnum::StructType(_) => {
                        // structs are passed by ref
                        BasicTypeEnum::PointerType(self.ptr_type).into()
                    }
                    BasicTypeEnum::VectorType(_) => todo!(),
                }
            })
            .collect::<Vec<BasicMetadataTypeEnum>>();

        let resolved_ret_type = &mir.types[function.ret];
        let fn_type = match resolved_ret_type {
            Type::Boolean => self.bool_type.fn_type(&parameters_types, false),
            Type::Function(_, _) => todo!(),
            Type::Struct(_, _) => {
                // structs are returned by ref
                self.ptr_type.fn_type(&parameters_types, false)
            }
            Type::Number => self.i64_type.fn_type(&parameters_types, false),
            Type::Void => self.void_type.fn_type(&parameters_types, false),
            Type::None => todo!(),
        };

        let fn_name = mangle(
            mir,
            function.identifier.id,
            function
                .parameters
                .iter()
                .map(|p| p.type_id)
                .collect::<Vec<TypeId>>()
                .as_slice(),
        );
        let f = self.module.add_function(&fn_name, fn_type, None);
        f.set_gc("shadow-stack");
        self.functions.insert(function.symbol_id, f);
    }

    fn gen_statement(&mut self, mir: &Mir, stmt: &Statement) -> Value<'ctx> {
        match &stmt.kind {
            StatementKind::Expression(expr_id) => {
                self.gen_expression(mir, &mir.expressions[*expr_id], true)
            }
            StatementKind::Ret(expr_id) => self.gen_ret(
                mir,
                expr_id.as_ref().map(|expr_id| &mir.expressions[*expr_id]),
            ),
        }
    }

    fn gen_ret(&mut self, mir: &Mir, expr: Option<&Expression>) -> Value<'ctx> {
        if let Some(expr) = expr {
            match self.gen_expression(mir, expr, true) {
                Value::Never => panic!(),
                Value::None => {
                    // this is used for implicit ret, where we can return nothing.
                    self.builder.build_return(None).unwrap();
                }
                Value::Number(val) => {
                    self.builder.build_return(Some(&val)).unwrap();
                }
                Value::Struct(val, _) => {
                    self.builder.build_return(Some(&val)).unwrap();
                }
            };
        } else {
            self.builder.build_return(None).unwrap();
        }
        Value::Never
    }

    fn gen_function_body(&mut self, mir: &Mir, function: &Function) -> Value<'ctx> {
        // It is ok for now to get a function by name, but this might need to change when we start
        // to mangle function names. When we do it, gen_function_signature() can return the function
        // value that we can reuse here.
        let llvm_function = self.functions[&function.symbol_id];

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
                BasicValueEnum::PointerValue(val) => val.set_name(&name),
                BasicValueEnum::StructValue(_) => unimplemented!("structs are passed by ref"),
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

        self.gen_expression(mir, &mir.expressions[function.body], true);

        Value::None
    }

    fn gen_variable(&mut self, mir: &Mir, variable: &Variable) {
        let llvm_type = self.repr(self.llvm_type(mir, variable.type_id));

        let ptr = self.gen_alloca(
            llvm_type,
            &format!(
                "{}#local#sym{}#",
                &mir.identifiers[variable.identifier.id], variable.symbol_id
            ),
            variable.symbol_id,
            None,
        );

        if matches!(
            mir.types[mir.symbols[variable.symbol_id].type_id],
            Type::Struct(_, _)
        ) {
            self.builder
                .build_store(ptr, self.ptr_type.const_zero())
                .unwrap();

            let layout = self.type_layouts[&mir.symbols[variable.symbol_id].type_id];

            self.builder
                .build_call(self.llvm_gcroot, &[ptr.into(), layout.into()], "gcroot")
                .unwrap();
        }
    }

    fn gen_expression(
        &mut self,
        mir: &Mir,
        expr: &Expression,
        must_create_gcroot: bool,
    ) -> Value<'ctx> {
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
                LiteralKind::Boolean(bool) => self.bool_type.const_int(*bool as u64, false).into(),
                LiteralKind::Identifier(symbol_id) => self.gen_expression_ident(mir, *symbol_id),
                LiteralKind::Number(number) => {
                    // todo:check check what happens for negative numbers
                    self.i64_type.const_int(*number as u64, false).into()
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
                self.gen_struct_instantiation(mir, *struct_id, fields, must_create_gcroot)
            }
        };

        #[cfg(debug_assertions)]
        {
            let t = &mir.types[expr.type_id];
            debug_assert!(
                t != &Type::None && value != Value::Never
                    || t == &Type::None && value == Value::Never,
                "{value:?} is of type {t:?}"
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
        let value = BasicValueEnum::from(self.gen_expression(mir, expr, false));

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

        #[cfg(any(test, feature = "gc-aggressive"))]
        self.builder.build_call(self.gc_run, &[], "gc_run").unwrap();

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
                    let value_ptr = *self.variables.get(symbol_id).unwrap();
                    let value_type = self.llvm_type(mir, mir.symbols[*symbol_id].type_id);
                    (value_ptr, value_type)
                }
                LiteralKind::Boolean(_) => panic!("a boolean is not a pointer"),
                LiteralKind::Number(_) => panic!("a number is not a pointer"),
            },
            ExpressionKind::Access(expr_id, symbol_id) => {
                let (struct_ptr_ptr, struct_type) =
                    self.gen_pointer_expression(mir, &mir.expressions[*expr_id]);

                // we need to dereference the variable or the field ptr to get the struct pointer
                let struct_ptr = self
                    .builder
                    .build_load(self.ptr_type, struct_ptr_ptr, "tmp")
                    .unwrap()
                    .into_pointer_value();

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
                let field_ptr = self
                    .builder
                    .build_struct_gep(struct_type, struct_ptr, index as u32, &name)
                    .unwrap();

                (field_ptr, self.llvm_type(mir, symbol.type_id))
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

        let cond = IntValue::from(self.gen_expression(mir, cond, true));
        self.builder
            .build_conditional_branch(cond, then_block, else_block)
            .unwrap();

        self.builder.position_at_end(then_block);
        let then_value = self.gen_expression(mir, true_branch, true);
        if !matches!(then_value, Value::Never) {
            self.builder.build_unconditional_branch(end_block).unwrap();
        }

        let else_value = match false_branch {
            None => Value::None,
            Some(false_branch) => {
                self.builder.position_at_end(else_block);

                let value = self.gen_expression(mir, false_branch, true);

                if !matches!(value, Value::Never) {
                    self.builder.build_unconditional_branch(end_block).unwrap();
                }

                value
            }
        };

        self.builder.position_at_end(end_block);
        match (then_value, else_value) {
            (Value::Never, Value::Never) => {
                self.builder.build_unreachable().unwrap();
                Value::Never
            }
            (Value::None, Value::Never) | (Value::Never, Value::None) => Value::None,
            (Value::Struct(then_value, then_type), Value::Struct(else_value, else_type)) => {
                debug_assert_eq!(then_type, else_type);
                let if_value = self
                    .builder
                    .build_phi(then_value.get_type(), "if_result")
                    .unwrap();
                if_value.add_incoming(&[(&then_value, then_block), (&else_value, else_block)]);
                Value::Struct(if_value.as_basic_value().into_pointer_value(), then_type)
            }
            // todo:check it seems strange: if one branch is "none" it means that it does not
            //  exist (cannot really hold for the then branch, but for the else it can. In that case
            //  the whole if expression cannot be of the other branch. At most, it can be an
            //  "option of" type
            (value, Value::None)
            | (value, Value::Never)
            | (Value::None, value)
            | (Value::Never, value) => value,
            (then_value, else_value) => {
                let then_value = BasicValueEnum::from(then_value);
                let else_value = BasicValueEnum::from(else_value);

                let if_value = self
                    .builder
                    .build_phi(then_value.get_type(), "if_result")
                    .unwrap();
                if_value.add_incoming(&[(&then_value, then_block), (&else_value, else_block)]);
                Value::from(if_value.as_basic_value())
            }
        }
    }

    fn gen_expression_ident(&self, mir: &Mir, symbol_id: SymbolId) -> Value<'ctx> {
        let symbol = &mir.symbols[symbol_id];
        let type_id = mir.symbols[symbol_id].type_id;
        let llvm_type = self.llvm_type(mir, type_id);

        if let Some(variable) = self.variables.get(&symbol_id) {
            let name = format!(
                "{}#local#sym{}#",
                mir.identifiers[mir.symbols[symbol_id].ident_id], symbol_id
            );

            if matches!(&mir.types[type_id], Type::Struct(_, _)) {
                return Value::Struct(
                    self.builder
                        .build_load(self.ptr_type, *variable, &name)
                        .unwrap()
                        .into_pointer_value(),
                    llvm_type,
                );
            }

            return Value::from(
                self.builder
                    .build_load(llvm_type, *variable, &name)
                    .unwrap(),
            );
        };

        match &symbol.kind {
            SymbolKind::Let(_) => {
                unreachable!("handled in the if variable.contains_key(..) above")
            }
            SymbolKind::LetFn(_, _, _) => todo!(),
            SymbolKind::Parameter(_, index) => {
                let value = self
                    .current_function()
                    .get_nth_param(*index as u32)
                    .unwrap();

                match self.llvm_type(mir, symbol.type_id) {
                    BasicTypeEnum::ArrayType(_) => todo!(),
                    BasicTypeEnum::FloatType(_) => todo!(),
                    BasicTypeEnum::IntType(_) => Value::from(value),
                    BasicTypeEnum::PointerType(_) => unimplemented!("pointers are not supported"),
                    BasicTypeEnum::StructType(struct_type) => {
                        Value::Struct(value.into_pointer_value(), struct_type.into())
                    }
                    BasicTypeEnum::VectorType(_) => todo!(),
                }
            }
            SymbolKind::Struct(_) => todo!(),
            SymbolKind::Field(_, _, _) => todo!(),
            SymbolKind::NativeType(_, _) => todo!(),
            SymbolKind::Native(_, _, _, _) => todo!(),
        }
    }

    fn gen_access(&mut self, mir: &Mir, expr_id: ExprId, symbol_id: SymbolId) -> Value<'ctx> {
        let symbol = &mir.symbols[symbol_id];
        let (ident_id, index) = match &symbol.kind {
            SymbolKind::Field(_, ident_id, index) => (*ident_id, *index),
            _ => panic!("invalid symbol type"),
        };

        match self.gen_expression(mir, &mir.expressions[expr_id], true) {
            Value::Struct(struct_pointer, struct_pointer_type) => {
                // we compute the pointer to the field
                let name = format!(
                    "{}.{}#idx{}#sym{}#",
                    struct_pointer.get_name().to_str().unwrap(),
                    &mir.identifiers[ident_id],
                    index,
                    symbol_id
                );

                let field_pointer = self
                    .builder
                    .build_struct_gep(struct_pointer_type, struct_pointer, index as u32, &name)
                    .unwrap();

                let symbol_llvm_type = self.llvm_type(mir, symbol.type_id);

                if matches!(mir.types[symbol.type_id], Type::Struct(_, _)) {
                    // the field is a struct type, we deref the field pointer to its value which is
                    // a pointer to a struct
                    let value = self
                        .builder
                        .build_load(self.ptr_type, field_pointer, &name)
                        .unwrap()
                        .into_pointer_value();
                    Value::Struct(value, symbol_llvm_type)
                } else {
                    // if the field holds the value, we dereference the field pointer to itss value
                    let value = self
                        .builder
                        .build_load(symbol_llvm_type, field_pointer, &name)
                        .unwrap();
                    debug_assert!(!matches!(value, BasicValueEnum::PointerValue(_)));
                    Value::from(value)
                }
            }
            value => panic!("invalid value: {:?}", value),
        }
    }

    fn gen_function_call(
        &mut self,
        mir: &Mir,
        symbol_id: SymbolId,
        params: &[ExprId],
    ) -> Value<'ctx> {
        let symbol = &mir.symbols[symbol_id];

        let return_type = match &symbol.kind {
            SymbolKind::Native(_, _, _, kind) if kind.is_instr() => {
                return kind.gen_instr(mir, self, params);
            }
            SymbolKind::Native(_, _, return_type, _) | SymbolKind::LetFn(_, _, return_type) => {
                match mir.types[*return_type] {
                    Type::Boolean | Type::Struct(_, _) | Type::Number => {
                        Some(self.llvm_type(mir, *return_type))
                    }
                    Type::Function(_, _) => todo!(),
                    Type::Void | Type::None => None,
                }
            }
            _ => panic!("callee muse be a function"),
        };

        let parameters = params
            .iter()
            .map(
                |e| match self.gen_expression(mir, &mir.expressions[*e], true) {
                    Value::None | Value::Never => panic!(),
                    Value::Number(val) => BasicMetadataValueEnum::IntValue(val),
                    Value::Struct(val, _) => BasicMetadataValueEnum::PointerValue(val),
                },
            )
            .collect::<Vec<BasicMetadataValueEnum>>();

        let function_name = &mir.identifiers[mir.symbols[symbol_id].ident_id];

        let called_function = self.functions[&symbol_id];

        self.builder
            .build_call(
                called_function,
                &parameters,
                &format!("{function_name}#res#",),
            )
            .unwrap()
            .try_as_basic_value()
            .left()
            .and_then(|ret| match return_type {
                None => None,
                Some(BasicTypeEnum::ArrayType(_)) => todo!(),
                Some(BasicTypeEnum::FloatType(_)) => todo!(),
                Some(BasicTypeEnum::IntType(_)) => Some(Value::from(ret)),
                Some(BasicTypeEnum::PointerType(_)) => unimplemented!("pointers are not supported"),
                Some(t @ BasicTypeEnum::StructType(_)) => {
                    Some(Value::Struct(ret.into_pointer_value(), t))
                }
                Some(BasicTypeEnum::VectorType(_)) => todo!(),
            })
            .unwrap_or(Value::None)
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
        let cond = BasicValueEnum::from(self.gen_expression(mir, cond, true)).into_int_value();
        self.builder
            .build_conditional_branch(cond, body_block, end_block)
            .unwrap();

        self.builder.position_at_end(body_block);
        let value = self.gen_expression(mir, body, true);
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
        must_create_gcroot: bool,
    ) -> Value<'ctx> {
        let name = format!(
            "heap#struct#{}#id{}#",
            &mir.identifiers[mir.structs[struct_id].identifier.id], struct_id
        );

        let struct_type = *self.struct_types.get(&struct_id).unwrap();
        let field_values = fields
            .iter()
            .map(
                |(_, expr_id)| match self.gen_expression(mir, &mir.expressions[*expr_id], true) {
                    Value::Number(val) => val.into(),
                    Value::Struct(pointer_value, _) => pointer_value.into(),
                    _ => panic!("value expected"),
                },
            )
            .collect::<Vec<BasicValueEnum>>();

        let gcroot = if must_create_gcroot {
            // todo:feature these gc root don't live for the whole of the frame, we can set them
            //   to null when the value is assigned to something else
            Some(self.create_gcroot(&name, mir.symbols[mir.structs[struct_id].symbol_id].type_id))
        } else {
            None
        };

        let struct_ptr = self
            .builder
            .build_call(
                self.malloc,
                &[struct_type.size_of().unwrap().as_basic_value_enum().into()],
                &name,
            )
            .unwrap()
            .try_as_basic_value()
            .left()
            .unwrap()
            .into_pointer_value();

        if let Some(gcroot) = gcroot {
            self.builder.build_store(gcroot, struct_ptr).unwrap();
        }

        for (index, value) in field_values.into_iter().enumerate() {
            let name = format!(
                "{}.{}#idx{}#sym{}",
                name,
                mir.identifiers[mir.structs[struct_id].fields[index].identifier.id],
                index,
                mir.structs[struct_id].fields[index].symbol_id
            );
            let field_ptr = self
                .builder
                .build_struct_gep(struct_type, struct_ptr, index as u32, &name)
                .unwrap();
            self.builder.build_store(field_ptr, value).unwrap();
        }

        Value::Struct(struct_ptr, struct_type.into())
    }

    fn create_gcroot(&self, for_name: &str, type_id: TypeId) -> PointerValue<'ctx> {
        let builder = self.context.create_builder();
        let first_basic_bloc = self.current_function().get_first_basic_block().unwrap();

        match first_basic_bloc.get_last_instruction() {
            None => {
                builder.position_at_end(first_basic_bloc);
            }
            Some(p) => {
                builder.position_at(self.current_function().get_first_basic_block().unwrap(), &p);
            }
        }

        let gcroot = builder
            .build_alloca(self.ptr_type, &format!("gcroot#{for_name}"))
            .unwrap();

        builder
            .build_store(gcroot, self.ptr_type.const_zero())
            .unwrap();

        let layout = self.type_layouts[&type_id];

        builder
            .build_call(self.llvm_gcroot, &[gcroot.into(), layout.into()], "gcroot")
            .unwrap();
        gcroot
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
            Type::Void => unreachable!("void is not a basic type"),
            Type::None => unreachable!("none is not a basic type"),
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

    fn repr(&self, llvm_type: BasicTypeEnum<'ctx>) -> BasicTypeEnum<'ctx> {
        match llvm_type {
            BasicTypeEnum::ArrayType(_) => self.ptr_type.into(),
            BasicTypeEnum::FloatType(_) => llvm_type,
            BasicTypeEnum::IntType(_) => llvm_type,
            BasicTypeEnum::PointerType(_) => unimplemented!("pointers are not supported"),
            BasicTypeEnum::StructType(_) => {
                // todo:feature small structs may be inlined
                self.ptr_type.into()
            }
            BasicTypeEnum::VectorType(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Value<'ctx> {
    Never,
    None,
    Number(IntValue<'ctx>),
    Struct(PointerValue<'ctx>, BasicTypeEnum<'ctx>),
}

impl<'ctx> From<BasicValueEnum<'ctx>> for Value<'ctx> {
    fn from(value: BasicValueEnum<'ctx>) -> Self {
        match value {
            BasicValueEnum::ArrayValue(_) => todo!(),
            BasicValueEnum::IntValue(val) => Self::from(val),
            BasicValueEnum::FloatValue(_) => todo!(),
            BasicValueEnum::PointerValue(_) => todo!(),
            BasicValueEnum::StructValue(_) => {
                unimplemented!("cannot construct a value from a struct, we miss the type")
            }
            BasicValueEnum::VectorValue(_) => todo!(),
        }
    }
}

impl<'ctx> From<IntValue<'ctx>> for Value<'ctx> {
    fn from(value: IntValue<'ctx>) -> Self {
        Self::Number(value)
    }
}

impl<'ctx> From<Value<'ctx>> for BasicValueEnum<'ctx> {
    fn from(value: Value<'ctx>) -> Self {
        match value {
            Value::Never | Value::None => panic!(),
            Value::Number(val) => val.into(),
            Value::Struct(val, _) => val.into(),
        }
    }
}

impl<'ctx> From<Value<'ctx>> for IntValue<'ctx> {
    fn from(value: Value<'ctx>) -> Self {
        match value {
            Value::Never => panic!(),
            Value::None => panic!(),
            Value::Number(val) => val,
            Value::Struct(_, _) => panic!(),
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
            NativeFnKind::PrintBoolean => false,
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
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_add(lhs, rhs, "add#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::SubNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_sub(lhs, rhs, "sub#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::MulNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_mul(lhs, rhs, "mul#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::DivNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_signed_div(lhs, rhs, "div#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::EqNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::NeqNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::NE, lhs, rhs, "ne#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::GtNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::SGT, lhs, rhs, "gt#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::LtNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::SLT, lhs, rhs, "lt#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::GeNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::SGE, lhs, rhs, "ge#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::LeNumberNumber => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::SLE, lhs, rhs, "le#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::EqBooleanBoolean => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::EQ, lhs, rhs, "eq#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::NeqBooleanBoolean => {
                let lhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[0]], true));
                let rhs =
                    IntValue::from(codegen.gen_expression(mir, &mir.expressions[params[1]], true));
                codegen
                    .builder
                    .build_int_compare(IntPredicate::NE, lhs, rhs, "ne#")
                    .unwrap()
                    .into()
            }
            NativeFnKind::PrintNumber => Value::None,
            NativeFnKind::PrintBoolean => Value::None,
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
        struct_assignment,
        r#"
        struct Struct { }
        let f(): number {
            let s = Struct { };
            1;
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
        struct_read_nested_field_var,
        r#"
        struct Inner { field: number }
        struct Outer { inner: Inner }
        let f(): number {
            let inner = Inner {
                field: 1
            };
            let outer = Outer {
                inner: inner
            };

            outer.inner.field;
        }
        "#
    );

    gen!(
        struct_read_nested_field,
        r#"
        struct Inner { field: number }
        struct Outer { inner: Inner }
        let f(): number {
            let outer = Outer {
                inner: Inner {
                    field: 1
                }
            };

            outer.inner.field;
        }
        "#
    );

    gen!(
        struct_read_field_const_struct,
        r#"
        struct Struct { field: number }
        let f() {
            let s = Struct {
                field: 1
            }.field;
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

    gen!(
        struct_as_parameter,
        r#"
        struct Struct { field: number }
        let f(s: Struct): number {
            s.field;
        }
        "#
    );

    gen!(
        struct_as_return,
        r#"
        struct Struct { field: number }
        let f(): Struct {
            Struct {
                field: 1
            };
        }
        "#
    );

    gen!(
        struct_var_as_parameter,
        r#"
        struct Struct { field: number }

        let f(s: Struct): number {
            s.field;
        }

        let g(): number {
            let s = Struct {
              field: 1
            };

            f(s);
        }
        "#
    );

    gen!(
        struct_lit_as_parameter,
        r#"
        struct Struct { field: number }

        let f(s: Struct): number {
            s.field;
        }

        let g(): number {
            f(
                Struct {
                    field: 1
                }
            );
        }
        "#
    );

    gen!(
        struct_returned_from_function,
        r#"
        struct Struct { field: number }

        let f(): number {
            let s = g();
            s.field;
        }

        let g(): Struct {
            Struct {
                field: 1
            };
        }
        "#
    );

    gen!(function_return_explicit_void, "let f() { ret; }");

    gen!(function_return_implicit_void, "let f() { }");

    gen!(
        function_call_void,
        r#"
        let g() {}
        let f() {
            g();
        }
        "#
    );
}
