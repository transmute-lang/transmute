use crate::interpreter::Value;
use crate::resolver::Type;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

pub struct Natives {
    functions: HashMap<&'static str, Vec<NativeFn>>,
    types: Vec<NativeType>,
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
            types: Default::default(),
        };

        natives.insert_fn(NativeFn {
            name: "neg",
            parameters: vec![Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let v = params.pop().unwrap().try_to_i64();
                Value::Number(-v)
            },
        });

        natives.insert_fn(NativeFn {
            name: "add",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left + right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "sub",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left - right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "mul",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left * right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "div",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left / right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "eq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left != right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "gt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left > right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "lt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left < right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "ge",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left >= right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "le",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left <= right)
            },
        });

        natives.insert_fn(NativeFn {
            name: "eq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left != right)
            },
        });

        natives.insert_type(NativeType {
            name: "boolean",
            ty: Type::Boolean,
        });
        natives.insert_type(NativeType {
            name: "number",
            ty: Type::Number,
        });
        natives.insert_type(NativeType {
            name: "void",
            ty: Type::Void,
        });

        natives
    }

    pub fn empty() -> Natives {
        Self {
            functions: Default::default(),
            types: Default::default(),
        }
    }

    fn insert_fn(&mut self, native: NativeFn) {
        if let Some(v) = self.functions.get_mut(native.name) {
            v.push(native);
        } else {
            self.functions.insert(native.name, vec![native]);
        }
    }

    fn insert_type(&mut self, native: NativeType) {
        self.types.push(native);
    }

    pub fn names(&self) -> Vec<String> {
        let mut names = self
            .functions
            .keys()
            .map(|s| s.to_string())
            .chain(self.types.iter().map(|native| native.name.to_string()))
            .collect::<Vec<String>>();
        names.sort();
        names.dedup();
        names
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
            .map(Native::Fn)
            .chain(self.types.into_iter().map(Native::Type))
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Native {
    Fn(NativeFn),
    Type(NativeType),
}

pub struct NativeFn {
    name: &'static str,
    parameters: Vec<Type>,
    return_type: Type,
    body: fn(Vec<Value>) -> Value,
}

impl NativeFn {
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
}

impl PartialEq<Self> for NativeFn {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for NativeFn {}

impl PartialOrd<Self> for NativeFn {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NativeFn {
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

impl Debug for NativeFn {
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

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct NativeType {
    name: &'static str,
    ty: Type,
}

impl NativeType {
    pub fn name(&self) -> &'static str {
        self.name
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
