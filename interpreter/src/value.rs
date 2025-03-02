use std::fmt::{Display, Formatter};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub enum Value {
    Boolean(bool),
    Number(i64),
    String(String),
    Struct(Vec<Ref>),
    Array(Vec<Ref>),
    #[default]
    Void,
}

impl Value {
    pub fn as_i64(&self) -> i64 {
        match self {
            Value::Number(n) => *n,
            _ => panic!("{} is not a number", self),
        }
    }

    pub fn as_bool(&self) -> bool {
        match self {
            Value::Boolean(b) => *b,
            _ => panic!("{} is not a bool", self),
        }
    }

    pub fn as_str(&self) -> &str {
        match self {
            Value::String(s) => s,
            _ => panic!("{} is not a string", self),
        }
    }

    pub fn as_struct(&self) -> &Vec<Ref> {
        match self {
            Value::Struct(v) => v,
            _ => panic!("{} is not a struct", self),
        }
    }

    pub fn as_mut_struct(&mut self) -> &mut Vec<Ref> {
        match self {
            Value::Struct(v) => v,
            _ => panic!("{} is not a struct", self),
        }
    }

    pub fn as_array(&self) -> &Vec<Ref> {
        match self {
            Value::Array(v) => v,
            _ => panic!("{} is not an array", self),
        }
    }

    pub fn as_mut_array(&mut self) -> &mut Vec<Ref> {
        match self {
            Value::Array(v) => v,
            _ => panic!("{} is not an array", self),
        }
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::Boolean(b) => {
                write!(f, "{b}")
            }
            Value::Number(n) => {
                write!(f, "{n}")
            }
            Value::String(s) => {
                write!(f, "{s}",)
            }
            Value::Void => {
                // todo:feature add support for escapes
                write!(f, "void")
            }
            Value::Struct(values) => {
                write!(f, "{{")?;
                for (index, value) in values.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", value)?;
                }
                write!(f, "}}")
            }
            Value::Array(values) => {
                write!(f, "[")?;
                for (index, value) in values.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", value)?;
                }
                write!(f, "]")
            }
        }
    }
}

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq)]
pub struct Ref(pub usize);

impl Display for Ref {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "*{}", self.0)
    }
}
