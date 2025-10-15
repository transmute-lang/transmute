use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use transmute_core::ids::{StmtId, TypeId};

// todo rethink the whole native idea: should it be parsed as everything else instead of being
//  defined here? this would allow the creation of a root `core` namespace where to put the
//  definitions. Once done:
//   - rename std.numbers to std.number (or to core.numbers?)
//   - rename std.booleans to std.boolean (or to core.booleans?)
//   - move std.native to core.native
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
            kind: NativeFnKind::NegNumber,
        });

        natives.insert_fn(NativeFn {
            name: "add",
            kind: NativeFnKind::AddNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "sub",
            kind: NativeFnKind::SubNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "mul",
            kind: NativeFnKind::MulNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "div",
            kind: NativeFnKind::DivNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "eq",
            kind: NativeFnKind::EqNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            kind: NativeFnKind::NeqNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "gt",
            kind: NativeFnKind::GtNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "lt",
            kind: NativeFnKind::LtNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "ge",
            kind: NativeFnKind::GeNumberNumber,
        });
        natives.insert_fn(NativeFn {
            name: "le",
            kind: NativeFnKind::LeNumberNumber,
        });

        natives.insert_fn(NativeFn {
            name: "eq",
            kind: NativeFnKind::EqBooleanBoolean,
        });
        natives.insert_fn(NativeFn {
            name: "neq",
            kind: NativeFnKind::NeqBooleanBoolean,
        });

        natives.insert_type(NativeType {
            name: Type::Boolean.identifier(),
            ty: Type::Boolean,
        });
        natives.insert_type(NativeType {
            name: Type::Number.identifier(),
            ty: Type::Number,
        });
        natives.insert_type(NativeType {
            name: Type::Void.identifier(),
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

    pub fn names(&self) -> Vec<&'static str> {
        let mut names = self
            .functions
            .keys()
            .chain(self.types.iter().map(|native| &native.name))
            .copied()
            .collect::<Vec<_>>();

        names.push(Type::Void.identifier());
        names.push(Type::Boolean.identifier());
        names.push(Type::Number.identifier());
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
    pub name: &'static str,
    pub kind: NativeFnKind,
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
        match self
            .kind
            .signature()
            .0
            .iter()
            .cmp(other.kind.signature().0.iter())
        {
            Ordering::Equal => {}
            o => return o,
        };
        self.kind.signature().1.cmp(&other.kind.signature().1)
    }
}

impl Debug for NativeFn {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "native#{}({}): {:?}",
            self.name,
            self.kind
                .signature()
                .0
                .iter()
                .map(|p| format!("{:?}", p))
                .collect::<Vec<String>>()
                .join(", "),
            self.kind.signature().1
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum NativeFnKind {
    NegNumber,
    AddNumberNumber,
    SubNumberNumber,
    MulNumberNumber,
    DivNumberNumber,
    EqNumberNumber,
    NeqNumberNumber,
    GtNumberNumber,
    LtNumberNumber,
    GeNumberNumber,
    LeNumberNumber,
    EqBooleanBoolean,
    NeqBooleanBoolean,
}

impl NativeFnKind {
    pub fn signature(&self) -> (&[Type], Type) {
        match self {
            NativeFnKind::NegNumber => (&[Type::Number], Type::Number),
            NativeFnKind::AddNumberNumber
            | NativeFnKind::SubNumberNumber
            | NativeFnKind::MulNumberNumber
            | NativeFnKind::DivNumberNumber => (&[Type::Number, Type::Number], Type::Number),
            NativeFnKind::EqNumberNumber
            | NativeFnKind::NeqNumberNumber
            | NativeFnKind::GtNumberNumber
            | NativeFnKind::LtNumberNumber
            | NativeFnKind::GeNumberNumber
            | NativeFnKind::LeNumberNumber => (&[Type::Number, Type::Number], Type::Boolean),
            NativeFnKind::EqBooleanBoolean | NativeFnKind::NeqBooleanBoolean => {
                (&[Type::Boolean, Type::Boolean], Type::Boolean)
            }
        }
    }
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub struct NativeType {
    pub name: &'static str,
    pub ty: Type,
}

#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Default)]
pub enum Type {
    /// The type is invalid
    Invalid,

    Boolean,
    Number,

    Function(Vec<TypeId>, TypeId),

    /// Represents a struct type. The `StmtId` determines what statement defined, the `Vec<TypeId>`
    /// the type parameters
    Struct(StmtId, Vec<TypeId>),
    Array(TypeId, usize),

    /// Represents an unbound `TypeParameter` type. The `StmtId` determines what statement defined
    /// it and the `usize` the position of the type parameter in the list.
    Parameter(StmtId, usize),

    /// The type of types
    Type,

    /// This value is used when the statement/expression does not have any value. This is the
    /// case for `namespace`, `let` and `let fn`.
    #[default]
    Void,

    /// This value is used when the statement/expression does not return any value. This is the
    /// case for `ret`.
    None,
}

impl Type {
    pub fn identifier(&self) -> &'static str {
        match self {
            Type::Invalid
            | Type::None
            | Type::Function(..)
            | Type::Struct(..)
            | Type::Array(..)
            | Type::Parameter(..)
            | Type::Type => unimplemented!(),
            Type::Boolean => "boolean",
            Type::Number => "number",
            Type::Void => "void",
        }
    }

    pub fn is_valid_return_type(&self) -> bool {
        matches!(self, Type::Void) || self.is_assignable()
    }

    pub fn is_assignable(&self) -> bool {
        matches!(
            self,
            Type::Boolean
                | Type::Number
                | Type::Function(_, _)
                | Type::Struct(_, _)
                | Type::Array(_, _)
                | Type::Parameter(_, _)
        )
    }

    pub fn as_parameter(&self) -> (StmtId, usize) {
        match self {
            Type::Parameter(stmt_id, index) => (*stmt_id, *index),
            t => panic!("expected a type parameter, got {t:?}"),
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Number => write!(f, "number"),
            Type::Function(..) => write!(f, "function"),
            Type::Struct(..) => write!(f, "struct"),
            Type::Array(_, len) => write!(f, "array[{len}]"),
            Type::Parameter(..) => write!(f, "type parameter"),
            Type::Type => write!(f, "type"),
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
