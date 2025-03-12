use transmute_mir::Type;

pub trait Allocation {
    fn is_heap_allocated(&self) -> bool;
}

impl Allocation for Type {
    fn is_heap_allocated(&self) -> bool {
        match self {
            Type::Boolean => false,
            Type::Number => false,
            Type::String => true,
            Type::Function(_, _) => todo!(),
            Type::Struct(_, _) => true,
            Type::Array(_, _) => true,
            Type::Void => unreachable!("void is not allocated"),
            Type::None => unreachable!("none is not allocated"),
        }
    }
}
