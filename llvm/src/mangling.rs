use std::borrow::Cow;
use transmute_core::ids::{FunctionId, IdentId, StructId, SymbolId, TypeId};
use transmute_mir::{Mir, Type};

const VERSION: u8 = 0;

pub fn mangle_function_name(
    mir: &Mir,
    ident_id: IdentId,
    parameters: &[TypeId],
    parent: Option<FunctionId>,
) -> String {
    mangle_function_name_internal(mir, ident_id, parameters, parent, 0)
}

fn mangle_function_name_internal(
    mir: &Mir,
    ident_id: IdentId,
    parameters: &[TypeId],
    parent: Option<FunctionId>,
    level: usize,
) -> String {
    let prefix = if level == 0 {
        Cow::Owned(format!("_TM{VERSION}_"))
    } else {
        Cow::Borrowed("")
    };

    let parent_mangled_name = parent
        .map(|fn_id| mangle_parent(mir, fn_id, level + 1))
        .unwrap_or(Cow::Borrowed(""));

    let identifier = mangle_identifier(&mir.identifiers[ident_id]);
    let parameters = mangle_parameters(mir, parameters);

    format!("{prefix}{parent_mangled_name}{identifier}{parameters}")
}

fn mangle_parent(mir: &Mir, function_id: FunctionId, level: usize) -> Cow<str> {
    let function = &mir.functions[function_id];
    let parent_name = mangle_function_name_internal(
        mir,
        function.identifier.id,
        &function
            .parameters
            .iter()
            .map(|p| p.type_id)
            .collect::<Vec<TypeId>>(),
        function.parent,
        level + 1,
    );
    Cow::Owned(format!("N{parent_name}",))
}

fn mangle_identifier(ident: &str) -> String {
    format!("{ident_len}{ident}", ident_len = ident.len())
}

fn mangle_parameters(mir: &Mir, parameters: &[TypeId]) -> String {
    let parameters_types = parameters
        .iter()
        .map(|t| mangle_type(mir, &mir.types[*t]))
        .collect::<Vec<Cow<'static, str>>>();
    format!(
        "{parameters_len}{parameters_types}",
        parameters_len = parameters_types.len(),
        parameters_types = parameters_types.join("")
    )
}

fn mangle_type(mir: &Mir, t: &Type) -> Cow<'static, str> {
    match t {
        Type::Boolean => Cow::Borrowed("b"),
        Type::Number => Cow::Borrowed("n"),
        Type::Function(_, _) => todo!(),
        Type::Struct(symbol_id, struct_id) => {
            Cow::Owned(mangle_struct_name(mir, *struct_id, *symbol_id))
        }
        Type::Array(type_id, len) => Cow::Owned(mangle_array_name(mir, *type_id, *len)),
        Type::Void => Cow::Borrowed("v"),
        Type::None => unimplemented!("none is not a valid type"),
    }
}

pub fn mangle_struct_name(mir: &Mir, struct_id: StructId, symbol_id: SymbolId) -> String {
    let parent_name = mir.structs[struct_id]
        .parent
        .map(|fn_id| mangle_parent(mir, fn_id, 0))
        .unwrap_or(Cow::Borrowed(""));

    let ident = mangle_identifier(&mir.identifiers[mir.symbols[symbol_id].ident_id]);
    format!("s{parent_name}{ident}")
}

pub fn mangle_array_name(mir: &Mir, type_id: TypeId, len: usize) -> String {
    format!("a{len}{t}", t = mangle_type(mir, &mir.types[type_id]))
}
