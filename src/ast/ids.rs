macro_rules! make_id {
    ($name:ident) => {
        #[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name {
            id: usize,
        }

        impl $name {
            pub fn id(&self) -> usize {
                self.id
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.id)
            }
        }

        impl From<usize> for $name {
            fn from(id: usize) -> Self {
                Self { id }
            }
        }
    };
}

pub(crate) use make_id;

make_id!(IdentId);
make_id!(IdentRefId);
make_id!(ExprId);
make_id!(StmtId);
make_id!(SymbolId);
