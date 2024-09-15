use std::borrow::Cow;
use transmute_core::ids::{IdentId, TypeId};
use transmute_mir::{Mir, Type};

const VERSION: u8 = 0;

// todo eventually will need to know the full path to structs and functions (inner ones, etc.)
// todo mangle struct names

pub fn mangle(mir: &Mir, ident_id: IdentId, parameters: &[TypeId]) -> String {
    let identifier = &mir.identifiers[ident_id];
    let parameters_types = parameters
        .iter()
        .map(|t| mangle_type(mir, &mir.types[*t]))
        .collect::<Vec<Cow<'static,str>>>();

    format!("_TM{VERSION}_{identifier_len}{identifier}{parameters_count}P{parameters_types}",
        identifier_len = identifier.len(),
        parameters_count= parameters_types.len(),
        parameters_types = parameters_types.join("")
    )
}

fn mangle_type(mir: &Mir, t: &Type) -> Cow<'static, str> {
    match t {
        Type::Boolean => Cow::Borrowed("b"),
        Type::Function(_, _) => todo!(),
        Type::Struct(symbol_id, _) => {
            let ident = &mir.identifiers[mir.symbols[*symbol_id].ident_id];
            Cow::Owned(format!("S{ident_len}{ident}", ident_len = ident.len()))
        }
        Type::Number => Cow::Borrowed("n"),
        Type::Void => Cow::Borrowed("v"),
        Type::None => unimplemented!("none is not a valid type"),
    }
}
