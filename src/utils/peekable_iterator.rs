use std::collections::VecDeque;
use std::ops::Index;
use std::vec::IntoIter;

pub struct PeekableIterator<I>
where
    I: Iterator,
{
    iter: I,
    buffer: VecDeque<I::Item>,
}

impl<I> PeekableIterator<I>
where
    I: Iterator,
{
    pub fn new<T>(iter: T) -> Self
    where
        T: IntoIterator<IntoIter = I>,
    {
        Self {
            iter: iter.into_iter(),
            buffer: VecDeque::new(),
        }
    }

    pub fn peek_nth(&mut self, n: usize) -> Option<&I::Item> {
        while self.buffer.len() < n.clone() + 1 {
            match self.iter.next() {
                Some(item) => self.buffer.push_back(item),
                None => return None,
            }
        }

        Some(&self.buffer[n])
    }
}

impl<I> Iterator for PeekableIterator<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.len() > 0 {
            self.buffer.pop_front()
        } else {
            self.iter.next()
        }
    }
}

impl<T> From<T> for PeekableIterator<T::IntoIter>
where
    T: IntoIterator,
{
    fn from(into_iter: T) -> Self {
        PeekableIterator::new(into_iter)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn next() {
        let iter = vec![0, 1];
        let mut peekable = PeekableIterator::new(iter);
        assert_eq!(peekable.next().unwrap(), 0);
        assert_eq!(peekable.next().unwrap(), 1);
        assert!(peekable.next().is_none());
    }

    #[test]
    fn peek_nth() {
        let iter = vec![0, 1];
        let mut peekable = PeekableIterator::new(iter);
        assert_eq!(peekable.peek_nth(0).unwrap(), &0);
        assert_eq!(peekable.peek_nth(1).unwrap(), &1);
        assert!(peekable.peek_nth(2).is_none());
    }

    #[test]
    fn peek_then_next() {
        let iter = vec![0, 1];
        let mut peekable = PeekableIterator::new(iter);
        peekable.peek_nth(1);
        assert_eq!(peekable.next().unwrap(), 0);
        assert_eq!(peekable.next().unwrap(), 1);
        assert!(peekable.next().is_none());
    }

    #[test]
    fn peek_next_peek_next() {
        let iter = vec![0, 1];
        let mut peekable = PeekableIterator::new(iter);
        peekable.peek_nth(0);
        assert_eq!(peekable.next().unwrap(), 0);
        peekable.peek_nth(0);
        assert_eq!(peekable.next().unwrap(), 1);
        assert!(peekable.next().is_none());
    }
}
