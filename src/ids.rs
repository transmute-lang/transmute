// todo move out of ast module, it's more generic that that

macro_rules! make_id {
    ($name:ident) => {
        #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
        pub struct $name {
            id: usize,
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", self.id)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}({})", stringify!($name), self.id)
            }
        }

        impl From<usize> for $name {
            fn from(id: usize) -> Self {
                Self { id }
            }
        }

        impl From<$name> for usize {
            fn from(id: $name) -> Self {
                id.id
            }
        }

        impl std::ops::Add<usize> for $name {
            type Output = $name;

            fn add(self, rhs: usize) -> Self::Output {
                Self::from(self.id + rhs)
            }
        }

        impl std::ops::Add<usize> for &$name {
            type Output = $name;

            fn add(self, rhs: usize) -> Self::Output {
                $name::from(self.id + rhs)
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
make_id!(TypeId);

macro_rules! id {
    ($e:expr) => {
        <_ as Into<usize>>::into($e)
    };
}

pub(crate) use id;
