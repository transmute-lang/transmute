use std::collections::hash_map::{Entry, Keys};
use std::collections::HashMap;
use std::fmt::{Debug, Formatter};
use std::hash::Hash;

#[derive(PartialEq, Default)]
pub struct IdMap<K: Eq + Hash, V> {
    inner: HashMap<K, V>,
}

impl<K: Eq + Hash, V> IdMap<K, V> {
    pub fn new() -> Self {
        Self {
            inner: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        self.inner.insert(key, value)
    }

    pub fn keys(&self) -> Keys<'_, K, V> {
        self.inner.keys()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        self.inner.get(key)
    }

    pub fn entry(&mut self, key: K) -> Entry<'_, K, V> {
        self.inner.entry(key)
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.inner.contains_key(key)
    }

    pub fn clear(&mut self) {
        self.inner.clear()
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)> {
        self.inner.get_key_value(key)
    }
}

// we manually implement debug to make sure the order of keys is consistent...
impl<K: Ord + Debug + Eq + Hash, V: Debug> Debug for IdMap<K, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.inner.is_empty() {
            return write!(f, "{{}}");
        }

        let mut keys = self.keys().collect::<Vec<_>>();
        keys.sort();

        writeln!(f, "{{")?;
        for expr_id in keys {
            let entry = self.get_key_value(expr_id).unwrap();
            writeln!(
                f,
                "    {:?}: {},",
                entry.0,
                format!("{:#?}", entry.1)
                    .split("\n")
                    .enumerate()
                    .map(|(i, l)| if i == 0 {
                        l.to_string()
                    } else {
                        format!("    {l}")
                    })
                    .collect::<Vec<_>>()
                    .join("\n")
            )?;
        }
        write!(f, "}}")
    }
}
