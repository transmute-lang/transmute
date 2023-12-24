use crate::ast::ids::IdentId;
use crate::ast::Ast;
use crate::interpreter::Value;
use crate::resolver::Type;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};

pub struct Natives {
    functions: HashMap<&'static str, Vec<NativeFn>>,
    types: HashMap<&'static str, NativeType>,
}

impl Default for Natives {
    fn default() -> Self {
        Natives::new()
    }
}

pub const TYPE_NUMBER: &str = "number";
pub const TYPE_BOOLEAN: &str = "boolean";
pub const TYPE_VOID: &str = "void";

impl Natives {
    pub fn new() -> Natives {
        let mut natives = Self::empty();

        natives.insert_fn(NativeFn {
            name: "neg",
            parameters: vec![TYPE_NUMBER],
            return_type: TYPE_NUMBER,
            body: |mut params| {
                let v = params.pop().unwrap().try_to_i64();
                Value::Number(-v)
            },
        });

        natives.insert_fn(NativeFn {
            name: "add",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_NUMBER,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left + right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "sub",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_NUMBER,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left - right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "mul",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_NUMBER,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left * right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "div",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_NUMBER,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Number(left / right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "eq",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left != right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "gt",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left > right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "lt",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left < right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "ge",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left >= right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "le",
            parameters: vec![TYPE_NUMBER, TYPE_NUMBER],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_i64();
                let left = params.pop().unwrap().try_to_i64();
                Value::Boolean(left <= right)
            },
        });

        natives.insert_fn(NativeFn {
            name: "eq",
            parameters: vec![TYPE_BOOLEAN, TYPE_BOOLEAN],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left == right)
            },
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            parameters: vec![TYPE_BOOLEAN, TYPE_BOOLEAN],
            return_type: TYPE_BOOLEAN,
            body: |mut params| {
                let right = params.pop().unwrap().try_to_bool();
                let left = params.pop().unwrap().try_to_bool();
                Value::Boolean(left != right)
            },
        });

        natives.insert_type(NativeType {
            name: TYPE_NUMBER,
            ty: Type::Number,
        });
        natives.insert_type(NativeType {
            name: TYPE_BOOLEAN,
            ty: Type::Boolean,
        });
        natives.insert_type(NativeType {
            name: TYPE_VOID,
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
        self.types.insert(native.name, native);
    }

    pub fn iterators(self) -> (NativeFnIterator, NativeTypeIterator) {
        let mut functions = self
            .functions
            .into_iter()
            .flat_map(|(_, natives)| natives.into_iter())
            .collect::<Vec<NativeFn>>();
        functions.sort();

        let mut types = self.types.into_values().collect::<Vec<NativeType>>();
        types.sort();

        (
            NativeFnIterator { values: functions },
            NativeTypeIterator { values: types },
        )
    }
}

impl From<&Natives> for Ast {
    fn from(natives: &Natives) -> Self {
        let mut identifiers = HashMap::<String, IdentId>::with_capacity(
            natives.functions.len() + natives.types.len(),
        );

        let mut names = natives
            .functions
            .keys()
            .map(|s| s.to_string())
            .collect::<Vec<String>>();
        names.sort();

        for name in names {
            if !identifiers.contains_key(&name) {
                let id = IdentId::from(identifiers.len());
                identifiers.insert(name, id);
            }
        }

        let mut names = natives
            .types
            .keys()
            .map(|s| s.to_string())
            .collect::<Vec<String>>();
        names.sort();

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
    }
}

pub struct NativeFn {
    name: &'static str,
    parameters: Vec<&'static str>,
    return_type: &'static str,
    body: fn(Vec<Value>) -> Value,
}

impl NativeFn {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn parameters(&self) -> &[&'static str] {
        &self.parameters
    }

    pub fn return_type(&self) -> &'static str {
        self.return_type
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
        self.return_type.cmp(other.return_type)
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

pub struct NativeFnIterator {
    values: Vec<NativeFn>,
}

impl Iterator for NativeFnIterator {
    type Item = NativeFn;

    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
    }
}

pub struct NativeType {
    name: &'static str,
    ty: Type,
}

impl NativeType {
    pub fn name(&self) -> &'static str {
        self.name
    }

    pub fn ty(&self) -> &Type {
        &self.ty
    }
}

impl PartialEq<Self> for NativeType {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for NativeType {}

impl PartialOrd<Self> for NativeType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NativeType {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(other.name)
    }
}

impl Debug for NativeType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "native-type#{}", self.name,)
    }
}

pub struct NativeTypeIterator {
    values: Vec<NativeType>,
}

impl Iterator for NativeTypeIterator {
    type Item = NativeType;

    fn next(&mut self) -> Option<Self::Item> {
        self.values.pop()
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
                let types = values.iter().map(|v| v.type_kind().to_string()).collect::<Vec<String>>();

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
