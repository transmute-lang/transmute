use crate::lexer::Lexer;
use crate::parser::Parser;
use std::{env, fs};
use jql::{Group, Selector};
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

    let groups = jql::selectors_parser("\"data\".\"key\" | ucase").unwrap();

    let selection = jql::groups_walker(&data, &groups);

    println!("{:?}", selection);

    // let groupGroup = selectors.remove(0);
    //
    // // let selector = group.selectors.remove(0);
    // for selector in group.selectors {
    //
    // }
    //
    // let mut value;
    // match selector {
    //     Selector::Array => {}
    //     Selector::Default(name) => {
    //         value = data.as_object().and_then(|o|o.get(&name))
    //     }
    //     Selector::Index(_) => {}
    //     Selector::Object(_) => {}
    //     Selector::Range(_) => {}
    // }


}
