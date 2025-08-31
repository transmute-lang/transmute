use std::borrow::Cow;
use transmute_core::id;
use transmute_core::ids::{IdentId, StructId, SymbolId, TypeId};
use transmute_mir::{Mir, ParentKind, Type};

const VERSION: u8 = 0;
const FUNCTION_PREFIX: &str = "F";
const NAMESPACE_PREFIX: &str = "N";

const TYPE_BOOLEAN: &str = "b";
const TYPE_NUMBER: &str = "n";
const TYPE_VOID: &str = "v";
const TYPE_STRUCT: &str = "s";
const TYPE_ARRAY: &str = "s";

pub fn mangle_function_name(
    mir: &Mir,
    ident_id: IdentId,
    parameters: &[TypeId],
    parent: ParentKind,
) -> String {
    mangle_function_name_internal(mir, ident_id, parameters, parent, 0)
}

fn mangle_function_name_internal(
    mir: &Mir,
    ident_id: IdentId,
    parameters: &[TypeId],
    parent: ParentKind,
    level: usize,
) -> String {
    let prefix = if level == 0 {
        Cow::Owned(format!("_TM{VERSION}_"))
    } else {
        Cow::Borrowed("")
    };

    let parent_mangled_name = mangle_parent(mir, parent, level + 1);

    let identifier = mangle_identifier(&mir.identifiers[ident_id]);
    let parameters = mangle_parameters(mir, parameters);

    format!("{prefix}{parent_mangled_name}{FUNCTION_PREFIX}{identifier}{parameters}")
}

fn mangle_parent(mir: &Mir, parent_kind: ParentKind, level: usize) -> Cow<str> {
    match parent_kind {
        ParentKind::Function(function_id) => {
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
            Cow::Owned(parent_name)
        }
        ParentKind::Namespace(namespace_id) => {
            if id!(namespace_id) == 0 {
                return Cow::Borrowed("");
            }

            let (parent, ident_id) = mir.namespaces[namespace_id];

            let parent_name = parent
                .map(|p| mangle_parent(mir, ParentKind::Namespace(p), level + 1))
                .unwrap_or(Cow::Borrowed(""));
            Cow::Owned(format!(
                "{parent_name}{NAMESPACE_PREFIX}{}",
                mangle_identifier(&mir.identifiers[ident_id])
            ))
        }
    }
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
        Type::Boolean => Cow::Borrowed(TYPE_BOOLEAN),
        Type::Number => Cow::Borrowed(TYPE_NUMBER),
        Type::Function(_, _) => todo!(),
        Type::Struct(symbol_id, struct_id) => {
            Cow::Owned(mangle_struct_name(mir, *struct_id, *symbol_id))
        }
        Type::Array(type_id, len) => Cow::Owned(mangle_array_name(mir, *type_id, *len)),
        Type::Void => Cow::Borrowed(TYPE_VOID),
        Type::None => unimplemented!("none is not a valid type"),
    }
}

pub fn mangle_struct_name(mir: &Mir, struct_id: StructId, symbol_id: SymbolId) -> String {
    let parent_name = mangle_parent(mir, mir.structs[struct_id].parent, 0);
    let ident = mangle_identifier(&mir.identifiers[mir.symbols[symbol_id].ident_id]);
    format!("{TYPE_STRUCT}{parent_name}{ident}")
}

pub fn mangle_array_name(mir: &Mir, type_id: TypeId, len: usize) -> String {
    format!(
        "{TYPE_ARRAY}{len}{t}",
        t = mangle_type(mir, &mir.types[type_id])
    )
}
