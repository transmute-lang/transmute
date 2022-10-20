extern crate core;

use crate::lexer::Lexer;
use crate::parser::Parser;
use std::{env, fs};
use jaq_core::{Ctx, Definitions, parse, RcIter, Val};
use serde_json::Value;

#[allow(dead_code)]
mod lexer;
#[allow(dead_code)]
mod parser;
#[allow(dead_code)]
mod utils;

fn main() {
    let data = "{\"data\": {\"key\":\"val\"}, \"non-data\": 12}";
    let data = serde_json::from_str::<Value>(data).unwrap();
    let query = "(.data.key2 // \"ok\") | isboolean";

    // start out only from core filters,
    // which do not include filters in the standard library
    // such as `map`, `select` etc.
    let mut defs = Definitions::core();
    let mut errs = Vec::new();
    for def in jaq_std::std() {
        defs.insert(def, &mut errs);
    }
    assert_eq!(errs, Vec::new());

    // parse the filter in the context of the given definitions
    let f = parse::parse(&query, parse::main()).0.unwrap();
    let f = defs.finish(f, Vec::new(), &mut errs);
    assert_eq!(errs, Vec::new());

    let inputs = RcIter::new(core::iter::empty());

    // iterator over the output values
    let mut out = f.run(Ctx::new([], &inputs), Val::from(data));

    for val in out {
        println!("{:?}", val);
    }
}
