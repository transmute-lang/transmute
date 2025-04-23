use crate::interpreter::Interpreter;
use crate::value::{Ref, Value};
use std::collections::HashMap;
use std::env;
use std::path::PathBuf;
use transmute_ast::parse;
use transmute_ast::pretty_print::Options;
use transmute_core::ids::IdentId;
use transmute_core::input::Input;
use transmute_hir::resolve;

mod interpreter;
pub mod natives;
pub mod value;

pub type Stack = Vec<HashMap<IdentId, Ref>>;
pub type Heap = Vec<Value>;

pub fn exec<S: Into<String>, C: NativeContext>(source: S, print_ast: bool, context: C) {
    let mut stdlib_src =
        PathBuf::from(env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is defined"));
    stdlib_src.push("src");
    stdlib_src.push("stdlib.tm");

    let inputs = vec![
        Input::core(),
        Input::try_from(stdlib_src).unwrap(),
        // fixme
        Input::from(("", source.into().leak() as &str)),
    ];

    let (inputs, result) = parse(inputs);
    if let Err(err) = result
        .peek(|ast| {
            if print_ast {
                let mut w = String::new();
                let _ = ast.pretty_print(&Options::default(), &mut w);
                print!("Parsed AST:\n{w}\n");
            }
        })
        .and_then(resolve)
        .map(|hir| Interpreter::new(&hir, context).start())
        .map_err(|d| d.with_inputs(inputs).to_string())
    {
        eprintln!("{err}")
    }
}

trait Peek<T, E> {
    fn peek<F: for<'a> Fn(&'a T)>(self, f: F) -> Result<T, E>;
}

impl<T, E> Peek<T, E> for Result<T, E> {
    fn peek<F: for<'a> Fn(&'a T)>(self, f: F) -> Result<T, E> {
        if let Ok(v) = &self {
            f(v)
        }
        self
    }
}

pub trait NativeContext {
    fn execute(
        &self,
        name: &str,
        parameters: &[Ref],
        stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref>;
}

#[cfg(test)]
mod tests {
    use insta_cmd::{assert_cmd_snapshot, get_cargo_bin};
    use std::env;
    use std::process::Command;

    macro_rules! exec {
        ($name:ident) => {
            #[test]
            fn $name() {
                // todo:test this requires that the binary already exists
                assert_cmd_snapshot!(Command::new(get_cargo_bin("tmi"))
                    .env(
                        "TRANSMUTE_STDLIB_PATH",
                        env::var("TRANSMUTE_STDLIB_PATH")
                            .expect("TRANSMUTE_STDLIB_PATH is defined")
                    )
                    .arg(concat!("../examples/", stringify!($name), ".tm"))
                    .arg("9"));
            }
        };
    }

    exec!(arrays_if);
    exec!(arrays_nested);
    exec!(arrays_of_structs);
    exec!(fibo_iter);
    exec!(fibo_rec);
    exec!(gc);
    exec!(inner_function);
    exec!(perimeter);
    exec!(perimeter_lit_struct);
    exec!(perimeter_var_struct);
    exec!(print);
    exec!(sibling_function);
    exec!(structs_anon);
    exec!(structs_fn);
    exec!(structs_inner);
    exec!(structs_nested);
    exec!(structs_of_arrays);
    exec!(structs_simple);
}
