use crate::interpreter::Interpreter;
use crate::value::Value;
use std::fs::File;
use std::path::PathBuf;
use transmute_ast::lexer::Lexer;
use transmute_ast::parser::Parser;
use transmute_ast::pretty_print::Options;
use transmute_hir::natives::Natives;
use transmute_hir::output::html::HtmlWriter;
use transmute_hir::UnresolvedHir;

mod interpreter;
pub mod value;

pub fn exec(src: &str, print_ast: bool, html_file_name: Option<PathBuf>, parameters: Vec<i64>) {
    let parameters = parameters
        .into_iter()
        .map(Value::Number)
        .collect::<Vec<Value>>();

    let result = Parser::new(Lexer::new(src))
        .parse()
        .peek(|ast| {
            if print_ast {
                let mut w = String::new();
                let _ = ast.pretty_print(&Options::default(), &mut w);
                print!("Parsed AST:\n{w}\n");
            }
        })
        .map(UnresolvedHir::from)
        .and_then(|hir| hir.resolve(Natives::new()))
        .peek(|ast| {
            if let Some(html_file_name) = &html_file_name {
                HtmlWriter::new(ast)
                    .write(&mut File::create(html_file_name).unwrap())
                    .unwrap();
            }
        })
        .map(|ast| Interpreter::new(&ast).start(parameters));

    match result {
        Ok(res) => {
            println!("Result: {}", res)
        }
        Err(err) => {
            print!("Errors:\n{}", err)
        }
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

#[cfg(test)]
mod tests {
    use insta_cmd::{assert_cmd_snapshot, get_cargo_bin};
    use std::process::Command;

    macro_rules! exec {
        ($name:ident) => {
            #[test]
            fn $name() {
                // todo:test this requires that the binary already exists
                assert_cmd_snapshot!(Command::new(get_cargo_bin("tmi"))
                    .arg(concat!("../examples/", stringify!($name), ".tm"))
                    .arg("9"));
            }
        };
    }

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
    exec!(structs_nested);
    exec!(structs_simple);
}
