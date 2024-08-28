use std::collections::hash_map::{IntoIter, ValuesMut};
use std::fmt::{Debug, Formatter};
use std::hash::{BuildHasher, Hash, RandomState};
use std::collections::HashMap as StdHashMap;

/// Delegates all used function to `std::collections::HashMap`, while providing an `Debug`
/// implementation that print entries by key in ascending order.
pub struct HashMap<K, V, S = RandomState> {
    base: StdHashMap<K, V, S>,
}

impl<K, V> HashMap<K, V, RandomState> {
    #[inline]
    pub fn new() -> HashMap<K, V, RandomState> {
        Default::default()
    }
}

impl<K, V, S> Default for HashMap<K, V, S>
    where
        S: Default,
{
    #[inline]
    fn default() -> HashMap<K, V, S> {
        Self {
            base: StdHashMap::with_hasher(Default::default()),
        }
    }
}

impl<K, V, S> HashMap<K, V, S> {
    #[inline]
   pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        self.base.values_mut()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }
}
impl<K, V, S> HashMap<K, V, S>
where
    K: Eq + Hash,
    S: BuildHasher,
{
    #[inline]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        self.base.insert(k, v)
    }

    #[inline]
    pub fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        self.base.extend(iter)
    }
}

impl<K, V, S> IntoIterator for HashMap<K, V, S> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;

    #[inline]
    fn into_iter(self) -> IntoIter<K, V> {
        self.base.into_iter()
    }
}

impl<K, V, S> Debug for HashMap<K, V, S>
where
    K: Debug + Ord,
    V: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut elements = self.base.iter().collect::<Vec<(&K, &V)>>();
        elements.sort_by(|e1, e2| e1.0.cmp(e2.0));

        f.debug_map().entries(elements).finish()
    }
}
