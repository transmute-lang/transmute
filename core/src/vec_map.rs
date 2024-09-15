use std::fmt::{Debug, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Index;

#[derive(PartialEq)]
pub struct VecMap<I, T> {
    vec: Vec<Option<T>>,
    index_type: PhantomData<I>,
}

impl<I, T> Debug for VecMap<I, T>
where
    I: Into<usize> + From<usize> + Debug,
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.vec.is_empty() {
            return write!(f, "[]");
        }

        writeln!(f, "[")?;

        for (i, v) in self.iter() {
            let element = if f.alternate() {
                format!("{i:?} => {:#?},", v)
            } else {
                format!("{i:?} => {:?},", v)
            };
            let element = element
                .lines()
                .map(|l| format!("    {l}"))
                .collect::<Vec<String>>()
                .join("\n");
            writeln!(f, "{}", element)?
        }

        write!(f, "]")?;

        Ok(())
    }
}

impl<I, T> VecMap<I, T> {
    pub fn is_empty(&self) -> bool {
        self.vec.iter().all(Option::is_none)
    }

    pub fn has_holes(&self) -> bool {
        self.vec.iter().any(|e| e.is_none())
    }

    /// Returns the number of elements in the vector, also referred to  as its 'length'.
    pub fn len(&self) -> usize {
        self.vec.len()
    }

    /// Make sure the `VecMap` can hold as many as `len` elements, fill empty slots with `None`.
    pub fn resize(&mut self, len: usize) {
        if self.vec.len() < len {
            self.vec.resize_with(len, || None);
        }
    }
}

impl<I, T> VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Create a new `VecMap` of capacity `size`
    pub fn with_capacity(size: usize) -> Self {
        Self {
            vec: Vec::with_capacity(size),
            index_type: PhantomData::<I>,
        }
    }

    pub fn with_reserved_capacity(size: usize) -> Self {
        let mut s = Self::with_capacity(size);
        s.resize(size);
        s
    }

    // todo refactoring: make use of create() in place of XId::from(x.len())
    pub fn create(&mut self) -> I {
        self.vec.push(None);
        (self.vec.len() - 1).into()
    }

    /// Insert the value at index.
    ///
    /// If the value at index was not already set, [`None`] is returned.
    ///
    /// If the value at index was present, the old value is returned.
    pub fn insert(&mut self, index: I, value: T) -> Option<T> {
        let index = index.into();
        self.resize(index + 1);
        let old = self.vec[index].take();
        self.vec[index] = Some(value);
        old
    }

    /// Appends the element at the end of the vec, even is some spaces are empty. Returns the
    /// index of the inserted element.
    pub fn push(&mut self, value: T) -> I {
        self.vec.push(Some(value));
        (self.vec.len() - 1).into()
    }

    /// Returns a reference to the value at index.
    pub fn get(&self, index: I) -> Option<&T> {
        match self.vec.get(index.into()) {
            None => None,
            Some(e) => e.as_ref(),
        }
    }

    /// Removes an element from the vector, returning the value at the index if the index was
    /// previously occupied.
    pub fn remove(&mut self, index: I) -> Option<T> {
        let index = index.into();
        if index >= self.vec.len() {
            None
        } else {
            self.vec[index].take()
        }
    }

    /// Returns the next element's index.
    pub fn next_index(&self) -> I {
        self.vec.len().into()
    }

    pub fn iter(&self) -> Iter<'_, I, T> {
        Iter {
            vec: self,
            index: 0,
        }
    }

    pub fn keys(&self) -> Vec<I> {
        self.vec
            .iter()
            .enumerate()
            .filter_map(|(index, v)| v.as_ref().map(|_| I::from(index)))
            .collect::<Vec<I>>()
    }

    pub fn into_reversed<B>(self) -> B
    where
        B: FromIterator<(T, I)>,
        T: Hash,
    {
        self.into_iter().map(|(i, ident)| (ident, i)).collect::<B>()
    }
}

impl<I, T> Default for VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<I, T> Index<I> for VecMap<I, T>
where
    I: Into<usize>,
{
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        let index = index.into();
        match &self.vec[index] {
            None => panic!("Index {index} is not not set"),
            Some(e) => e,
        }
    }
}

impl<I, T> Index<I> for &VecMap<I, T>
where
    I: Into<usize>,
{
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        let index = index.into();
        match &self.vec[index] {
            None => panic!("Index {index} is not not set"),
            Some(e) => e,
        }
    }
}

pub struct Iter<'a, I, T>
where
    I: Into<usize> + From<usize>,
{
    vec: &'a VecMap<I, T>,
    index: usize,
}

impl<'a, I, T> Iterator for Iter<'a, I, T>
where
    I: Into<usize> + From<usize>,
{
    type Item = (I, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.vec.len();
        while self.index < len {
            let index = self.index;
            self.index += 1;

            if let Some(e) = self.vec.get(index.into()) {
                return Some((index.into(), e));
            }
        }
        None
    }
}

impl<I, T> IntoIterator for VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    type Item = (I, T);
    type IntoIter = IntoIter<I, T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            vec: self,
            index: 0,
        }
    }
}

pub struct IntoIter<I: Into<usize> + From<usize>, T> {
    vec: VecMap<I, T>,
    index: usize,
}

impl<'a, I, T> IntoIterator for &'a VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    type Item = (I, &'a T);
    type IntoIter = Iter<'a, I, T>;

    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter {
            vec: self,
            index: 0,
        }
    }
}

impl<I, T> Iterator for IntoIter<I, T>
where
    I: Into<usize> + From<usize>,
{
    type Item = (I, T);

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.vec.len();
        while self.index < len {
            let index = self.index;
            self.index += 1;

            if let Some(e) = self.vec.remove(index.into()) {
                return Some((index.into(), e));
            }
        }
        None
    }
}

impl<I, T> From<Vec<T>> for VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    fn from(value: Vec<T>) -> Self {
        let mut ret = Self::with_capacity(value.len());
        for v in value {
            ret.push(v);
        }
        ret
    }
}

impl<I, T> FromIterator<(I, T)> for VecMap<I, T>
where
    I: Into<usize> + From<usize>,
{
    fn from_iter<IT: IntoIterator<Item = (I, T)>>(iter: IT) -> Self {
        let mut vec = VecMap::new();
        for (index, value) in iter {
            vec.insert(index, value);
        }
        vec
    }
}

impl<I, T> TryFrom<VecMap<I, T>> for Vec<T>
where
    I: Into<usize> + From<usize>,
{
    type Error = Vec<usize>;

    /// Tries to convert to a vec.
    ///
    /// If the sparse vec contains indices with not values, an [`Err`] is returned, which contains
    /// the empty indices list
    fn try_from(value: VecMap<I, T>) -> Result<Self, Self::Error> {
        let mut empty = Vec::new();
        let mut vec = Vec::with_capacity(value.len());
        for (i, v) in value.vec.into_iter().enumerate() {
            match v {
                None => empty.push(i),
                Some(v) => vec.push(v),
            }
        }
        if empty.is_empty() {
            Ok(vec)
        } else {
            Err(empty)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn with_capacity() {
        let vec = VecMap::<usize, i32>::with_reserved_capacity(1);
        assert_eq!(vec.len(), 1);
    }

    #[test]
    fn resize() {
        let mut vec = VecMap::<usize, i32>::new();
        assert_eq!(vec.len(), 0);
        vec.resize(1);
        assert_eq!(vec.len(), 1);
    }

    #[test]
    fn get_out_of_bound() {
        let vec = VecMap::<usize, i32>::new();
        let ret = vec.get(42usize);
        assert_eq!(ret, None);
    }

    #[test]
    fn get() {
        let vec = VecMap::<usize, i32>::with_capacity(1);
        let ret = vec.get(0usize);
        assert_eq!(ret, None);
    }

    #[test]
    fn insert_get() {
        let mut vec = VecMap::<usize, i32>::default();
        vec.insert(0usize, 42);
        let ret = vec.get(0usize);
        assert_eq!(ret, Some(&42));
    }

    #[test]
    fn push_get() {
        let mut vec = VecMap::<usize, i32>::default();
        let index = vec.push(42);
        assert_eq!(index, 0usize);
        let ret = vec.get(0usize);
        assert_eq!(ret, Some(&42));
    }

    #[test]
    fn remove() {
        let mut vec = VecMap::<usize, i32>::default();
        vec.push(42);
        let ret = vec.remove(0);
        assert_eq!(ret, Some(42));
    }

    #[test]
    fn remove_out_of_bound() {
        let mut vec = VecMap::<usize, i32>::default();
        let ret = vec.remove(0);
        assert_eq!(ret, None);
    }

    #[test]
    fn next_index() {
        let mut vec = VecMap::<usize, i32>::default();
        let next = vec.next_index();
        assert_eq!(next, 0usize);
        vec.push(42);
        let next = vec.next_index();
        assert_eq!(next, 1usize);
    }

    #[test]
    fn into_reversed() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push("hello");
        vec.insert(2, "world");

        let hashmap = vec.into_reversed::<HashMap<_, _>>();
        assert_eq!(hashmap.len(), 2);
        assert_eq!(hashmap.get("hello"), Some(&0));
        assert_eq!(hashmap.get("world"), Some(&2));
    }

    #[test]
    fn trait_index_ref_sparsevec() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);

        let ret = &vec[0];

        assert_eq!(ret, &42);
    }

    #[test]
    fn trait_from_vec_to_sparsevec() {
        let vec = vec![42];
        let vec = VecMap::<usize, _>::from(vec);
        assert_eq!(vec.len(), 1);
        assert_eq!(vec[0], 42);
    }

    #[test]
    fn trait_try_from_sparsevec_to_vec_no_empty() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);
        let vec = Vec::try_from(vec).unwrap();
        assert_eq!(vec.len(), 1);
        assert_eq!(vec[0], 42);
    }

    #[test]
    fn trait_try_from_sparsevec_to_vec_with_empty() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);
        vec.insert(2, 43);
        let vec = Vec::try_from(vec).unwrap_err();
        assert_eq!(vec.len(), 1);
        assert_eq!(vec[0], 1);
    }

    #[test]
    fn into_iter() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);
        vec.insert(2, 43);

        let vec = vec.into_iter().collect::<Vec<(usize, i32)>>();

        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0], (0, 42));
        assert_eq!(vec[1], (2, 43));
    }

    #[test]
    fn iter() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);
        vec.insert(2, 43);

        let vec = vec
            .iter()
            .map(|(i, v)| (i, *v))
            .collect::<Vec<(usize, i32)>>();

        assert_eq!(vec.len(), 2);
        assert_eq!(vec[0], (0, 42));
        assert_eq!(vec[1], (2, 43));
    }

    #[test]
    fn iter_ref() {
        let mut vec = VecMap::<usize, _>::new();
        vec.push(42);
        vec.insert(2, 43);

        let mut target = Vec::new();
        for val in &vec {
            target.push((val.0, *val.1));
        }

        assert_eq!(target.len(), 2);
        assert_eq!(target[0], (0, 42));
        assert_eq!(target[1], (2, 43));

        vec.push(44); // we did not lose the ownership
    }

    #[test]
    fn has_holes() {
        let mut vec = VecMap::new();

        vec.insert(1usize, 1);
        assert!(vec.has_holes());

        vec.insert(0usize, 1);
        assert!(!vec.has_holes());
    }

    #[test]
    fn collect_from_pair() {
        let pairs = vec![(0usize, 42), (2usize, 43)];

        let vec = pairs.into_iter().collect::<VecMap<usize, i32>>();

        assert_eq!(vec.len(), 3);
        assert_eq!(vec[0], 42);
        assert_eq!(vec.get(1), None);
        assert_eq!(vec[2], 43);
    }
}
