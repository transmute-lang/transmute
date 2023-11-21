use std::fmt::{Display, Formatter};

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

        impl Display for $name {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
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

make_id!(IdentId);
make_id!(IdentRefId);
make_id!(ExprId);
make_id!(StmtId);
make_id!(SymbolId);
make_id!(ScopeId);

// todo implement IdVec?
