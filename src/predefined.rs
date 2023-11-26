use crate::interpreter::Value;
use crate::type_check::Type;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

pub struct Predefined {
    functions: HashMap<&'static str, Vec<PredefinedFn>>,
}

impl Default for Predefined {
    fn default() -> Self {
        Predefined::new()
    }
}

impl Predefined {
    pub fn new() -> Predefined {
        let mut predef = Self {
            functions: Default::default(),
        };

        predef.insert_fn(PredefinedFn {
            name: "neg",
            parameters: vec![Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let v = params.pop().unwrap().try_to_i64();
                Value::Number(-v)
            },
        });

        predef.insert_fn(PredefinedFn {
            name: "add",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left + right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "sub",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left - right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "mul",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left * right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "div",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Number,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left / right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "eq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left == right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "neq",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left != right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "gt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left > right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "lt",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left < right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "ge",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left >= right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "le",
            parameters: vec![Type::Number, Type::Number],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left <= right)
            },
        });

        predef.insert_fn(PredefinedFn {
            name: "eq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left == right)
            },
        });
        predef.insert_fn(PredefinedFn {
            name: "neq",
            parameters: vec![Type::Boolean, Type::Boolean],
            return_type: Type::Boolean,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left != right)
            },
        });

        predef
    }

    fn insert_fn(&mut self, predef: PredefinedFn) {
        if let Some(v) = self.functions.get_mut(predef.name) {
            v.push(predef);
        } else {
            self.functions.insert(predef.name, vec![predef]);
        }
    }

    pub fn find_fn(&self, ident: &str, parameters: Vec<Type>) -> Option<&PredefinedFn> {
        if let Some(function) = self.functions.get(ident) {
            function.iter().find(|f| f.parameters == parameters)
        } else {
            None
        }
    }
}

pub struct PredefinedFn {
    name: &'static str,
    parameters: Vec<Type>,
    return_type: Type,
    body: fn(Vec<Value>) -> Value,
}

impl PredefinedFn {
    pub fn return_type(&self) -> Type {
        self.return_type
    }

    pub fn apply(&self, parameters: Vec<Value>) -> Value {
        (self.body)(parameters)
    }
}

impl Debug for PredefinedFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "native[{}({}): {:?}]",
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
    use crate::interpreter::Value;
    use crate::predefined::Predefined;
    use crate::type_check::Type;

    macro_rules! predef {
        ($name:ident: $function:expr, [$($value:expr,)*] => $expected:expr) => {
            #[test]
            fn $name() {
                let predef = Predefined::default();
                let values = vec![$($value),*];
                let types = values.iter().map(|v| v.ty()).collect::<Vec<Type>>();

                let actual = predef
                    .find_fn($function, types)
                    .unwrap()
                    .apply(values);

                assert_eq!(actual, $expected);
            }
        };
    }

    predef!(neg_number: "neg", [Value::Number(1),] => Value::Number(-1));

    predef!(add_number_number: "add", [Value::Number(1), Value::Number(2),] => Value::Number(3));
    predef!(sum_number_number: "sub", [Value::Number(1), Value::Number(2),] => Value::Number(-1));
    predef!(mul_number_number: "mul", [Value::Number(1), Value::Number(2),] => Value::Number(2));
    predef!(div_number_number: "div", [Value::Number(1), Value::Number(2),] => Value::Number(0));
    predef!(gt_number_number: "gt", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    predef!(ge_number_number: "ge", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    predef!(lt_number_number: "lt", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));
    predef!(le_number_number: "le", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));
    predef!(eq_number_number_false: "eq", [Value::Number(1), Value::Number(2),] => Value::Boolean(false));
    predef!(eq_number_number_true: "eq", [Value::Number(1), Value::Number(1),] => Value::Boolean(true));
    predef!(neq_number_number_false: "neq", [Value::Number(1), Value::Number(1),] => Value::Boolean(false));
    predef!(neq_number_number_true: "neq", [Value::Number(1), Value::Number(2),] => Value::Boolean(true));

    predef!(eq_boolean_boolean_false: "eq", [Value::Boolean(true), Value::Boolean(false),] => Value::Boolean(false));
    predef!(eq_boolean_boolean_true: "eq", [Value::Boolean(true), Value::Boolean(true),] => Value::Boolean(true));
    predef!(neq_boolean_boolean_false: "neq", [Value::Boolean(false), Value::Boolean(false),] => Value::Boolean(false));
    predef!(neq_boolean_boolean_true: "neq", [Value::Boolean(true), Value::Boolean(false),] => Value::Boolean(true));
}
