use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt::{Debug, Display, Formatter};
use transmute_core::ids::{StmtId, TypeId};

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
        natives.insert_type(NativeType {
            name: Type::String.identifier(),
            ty: Type::String,
        });

        #[cfg(feature = "gc-functions")]
        {
            natives.insert_fn(NativeFn {
                name: "gc_run",
                kind: NativeFnKind::GcRun,
            });
            natives.insert_fn(NativeFn {
                name: "gc_stats",
                kind: NativeFnKind::GcStats,
            });
        }

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

        // todo:refactoring maybe do it somewhere else?
        names.push(Type::Void.to_string());
        names.push(Type::Boolean.to_string());
        names.push(Type::Number.to_string());
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
    //todo:feature is it still needed?
    #[cfg(feature = "gc-functions")]
    GcRun,
    //todo:feature is it still needed?
    #[cfg(feature = "gc-functions")]
    GcStats,
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
            #[cfg(feature = "gc-functions")]
            NativeFnKind::GcRun | NativeFnKind::GcStats => (&[], Type::Void),
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
    // todo:refactor:string: this is probably naive and must be generalized somehow: we don't want to have to
    //  `Type` for each type the std lib provides (think List, Map, etc.) some mechanism might be
    //  an annotation on structs defined in "transmute" in the stdlib. Something along the lines of
    //  `native struct String {};`. This would be parsed, but no emitted as LLVM-IR.
    String,

    Function(Vec<TypeId>, TypeId),

    Struct(StmtId),
    Array(TypeId, usize),

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
            Type::Invalid
            | Type::None
            | Type::Function(..)
            | Type::Struct(..)
            | Type::Array(..) => unimplemented!(),
            Type::Boolean => "boolean",
            Type::Number => "number",
            Type::String => "string",
            Type::Void => "void",
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Type::Boolean => write!(f, "boolean"),
            Type::Number => write!(f, "number"),
            Type::String => write!(f, "string"),
            Type::Function(..) => write!(f, "function"),
            Type::Struct(..) => write!(f, "struct"),
            Type::Array(_, len) => write!(f, "array[{len}]"),
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
            "string" => Ok(Type::String),
            "void" => Ok(Type::Void),
            &_ => Err(format!("'{}' is not a known type", value)),
        }
    }
}
