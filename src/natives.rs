use crate::ast::ids::IdentId;
use crate::ast::{Ast, WithoutImplicitRet};
use crate::desugar::ImplicitRet;
use crate::interpreter::Value;
use crate::resolver::Type;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

pub struct Natives {
    functions: HashMap<&'static str, Vec<Native>>,
}

impl Default for Natives {
    fn default() -> Self {
        Natives::new()
    }
}

impl Natives {
    pub fn new() -> Natives {
        let mut natives = Self {
            functions: Default::default(),
        };

        natives.insert_fn(Native {
            name: "neg",
            parameters: vec![Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let v = params.pop().unwrap().try_to_i64();
                Value::Number(-v)
            },
        });

        natives.insert_fn(Native {
            name: "add",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left + right)
            },
        });
        natives.insert_fn(Native {
            name: "sub",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left - right)
            },
        });
        natives.insert_fn(Native {
            name: "mul",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left * right)
            },
        });
        natives.insert_fn(Native {
            name: "div",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left / right)
            },
        });
        natives.insert_fn(Native {
            name: "eq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(Native {
            name: "neq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left != right)
            },
        });
        natives.insert_fn(Native {
            name: "gt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left > right)
            },
        });
        natives.insert_fn(Native {
            name: "lt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left < right)
            },
        });
        natives.insert_fn(Native {
            name: "ge",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left >= right)
            },
        });
        natives.insert_fn(Native {
            name: "le",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left <= right)
            },
        });

        natives.insert_fn(Native {
            name: "eq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(Native {
            name: "neq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left != right)
            },
        });

        natives
    }

    pub fn empty() -> Natives {
        Self {
            functions: Default::default(),
        }
    }

    fn insert_fn(&mut self, native: Native) {
        if let Some(v) = self.functions.get_mut(native.name) {
            v.push(native);
        } else {
            self.functions.insert(native.name, vec![native]);
        }
    }
}

impl From<&Natives> for Ast<WithoutImplicitRet> {
    fn from(natives: &Natives) -> Self {
        let mut names = natives
            .functions
            .keys()
            .map(|s| s.to_string())
            .collect::<Vec<String>>();
        names.sort();

        let mut identifiers = HashMap::<String, IdentId>::with_capacity(natives.functions.len());

        for name in names {
            if !identifiers.contains_key(&name) {
                let id = IdentId::from(identifiers.len());
                identifiers.insert(name, id);
            }
        }

        let mut identifiers = identifiers.into_iter().collect::<Vec<(String, IdentId)>>();

        identifiers.sort_by(|(_, id1), (_, id2)| id1.id().cmp(&id2.id()));

        let identifiers = identifiers
            .into_iter()
            .map(|(ident, _)| ident)
            .collect::<Vec<String>>();

        Ast::new(identifiers, vec![], vec![], vec![], vec![])
            .convert_implicit_ret(ImplicitRet::new())
    }
}

impl IntoIterator for Natives {
    type Item = Native;
    type IntoIter = NativeIterator;

    fn into_iter(self) -> Self::IntoIter {
        let mut values = self
            .functions
            .into_iter()
            .flat_map(|(_, natives)| natives.into_iter())
            .collect::<Vec<Native>>();
        values.sort();
        NativeIterator { values }
    }
}

pub struct NativeIterator {
    values: Vec<Native>,
}

impl Iterator for NativeIterator {
    type Item = Native;

    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

pub struct Native {
    name: &'static str,
    parameters: Vec<Type>,
    return_type: Type,
    body: fn(Vec<Value>) -> Value,
}

impl Native {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn parameters(&self) -> &Vec<Type> {
        &self.parameters
    }

    pub fn return_type(&self) -> &Type {
        &self.return_type
    }

    pub fn body(self) -> fn(Vec<Value>) -> Value {
        self.body
    }

    // pub fn apply(&self, parameters: Vec<Value>) -> Value {
    //     (self.body)(parameters)
    // }
}

impl PartialEq<Self> for Native {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Native {}

impl PartialOrd<Self> for Native {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Native {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.name.cmp(other.name) {
            Ordering::Equal => {}
            o => return o,
        };
        match self.parameters.iter().cmp(other.parameters.iter()) {
            Ordering::Equal => {}
            o => return o,
        };
        self.return_type.cmp(&other.return_type)
    }
}

impl Debug for Native {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "native#{}({}): {:?}",
            self.name,
            self.parameters
                .iter()
                .map(|p| format!("{:?}", p))
                .collect::<Vec<String>>()
                .join(", "),
            self.return_type
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! native {
        ($name:ident: $function:expr, [$($value:expr,)*] => $expected:expr) => {
            #[test]
            fn $name() {
                let native = Natives::default();
                let values = vec![$($value),*];
                let types = values.iter().map(|v| v.ty()).collect::<Vec<Type>>();

                let f = if let Some(function) = native.functions.get($function) {
                    function.iter().find(|f| f.parameters == types)
                } else {
                    None
                };

                let actual = (f
                    .unwrap()
                    .body)(values);

                assert_eq!(actual, $expected);
            }
        };
    }

    native!(neg_number: "neg", [Value::Number(1),] => Value::Number(-1));

    native!(add_number_number: "add", [Value::Number(1), Value::Number(2),] => Value::Number(3));
    native!(sum_number_number: "sub", [Value::Number(1), Value::Number(2),] => Value::Number(-1));
    native!(mul_number_number: "mul", [Value::Number(1), Value::Number(2),] => Value::Number(2));
    native!(div_number_number: "div", [Value::Number(1), Value::Number(2),] => Value::Number(0));
    native!(gt_number_number: "gt", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    native!(ge_number_number: "ge", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    native!(lt_number_number: "lt", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));
    native!(le_number_number: "le", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));
    native!(eq_number_number_false: "eq", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    native!(eq_number_number_true: "eq", [Value::Number(1), Value::Number(1),] => Value::Boolean(true));
    native!(neq_number_number_false: "neq", [Value::Number(1), Value::Number(1),] => Value::Boolean(false));
    native!(neq_number_number_true: "neq", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));

    native!(eq_boolean_boolean_false: "eq", [Value::Boolean(true), Value::Boolean(false),] => Value::Boolean(false));
    native!(eq_boolean_boolean_true: "eq", [Value::Boolean(true), Value::Boolean(true),] => Value::Boolean(true));
    native!(neq_boolean_boolean_false: "neq", [Value::Boolean(false), Value::Boolean(false),] => Value::Boolean(false));
    native!(neq_boolean_boolean_true: "neq", [Value::Boolean(true), Value::Boolean(false),] => Value::Boolean(true));
}
