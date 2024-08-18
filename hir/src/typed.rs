use std::fmt::{Debug, Display, Formatter};
use transmute_core::ids::{StmtId, TypeId};

pub trait TypedState {}

#[derive(Debug)]
pub struct Untyped;

impl TypedState for Untyped {}

#[derive(Clone)]
pub struct Typed(pub TypeId);

impl TypedState for Typed {}

impl Debug for Typed {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Typed({})", self.0)
    }
}

// todo think about it being in Native
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub enum Type {
    /// The type is invalid
    Invalid, // todo can we remove that from HIR? Or lower HIR to MIR to get rid of it...

    Boolean,
    Function(Vec<TypeId>, TypeId),
    Struct(StmtId),
    Number,

    /// This value is used when the statement/expression does not have any value. This is the
    /// case for `let` and `let fn`.
    #[default]
    Void,

    /// This value is used when the statement/expression does not return any value. This is the
    /// case for `ret`.
    None,
}

impl Type {
    pub fn identifier(&self) -> &'static str {
        match self {
            Type::Invalid | Type::None | Type::Function(..) | Type::Struct(..) => unimplemented!(),
            Type::Boolean => "boolean",
            Type::Number => "number",
            Type::Void => "void",
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Function(..) => write!(f, "function"),
            Type::Struct(..) => write!(f, "struct"),
            Type::Number => write!(f, "number"),
            Type::Void => write!(f, "void"),
            Type::None => write!(f, "no type"),
            Type::Invalid => write!(f, "invalid"),
        }
    }
}

impl TryFrom<&str> for Type {
    type Error = String;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        match value {
            "boolean" => Ok(Type::Boolean),
            "number" => Ok(Type::Number),
            "void" => Ok(Type::Void),
            &_ => Err(format!("'{}' is not a known type", value)),
        }
    }
}
