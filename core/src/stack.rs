pub use std::slice::Iter;

#[derive(Debug, Default)]
pub struct Stack<T> {
    stack: Vec<T>,
}

impl<T> Stack<T> {
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn len(&self) -> usize {
        self.stack.len()
    }

    pub fn push(&mut self, item: T) {
        self.stack.push(item);
    }

    pub fn pop(&mut self) {
        debug_assert!(!self.stack.is_empty(), "stack is empty");
        self.stack.pop();
    }

    pub fn last(&self) -> Option<&T> {
        self.stack.last()
    }

    pub fn last_mut(&mut self) -> Option<&mut T> {
        self.stack.last_mut()
    }

    pub fn root(&self) -> Option<&T> {
        self.stack.first()
    }

    pub fn iter(&self) -> Iter<'_, T> {
        self.stack.iter()
    }
}

impl<T: Default> Stack<T> {
    pub fn push_default(&mut self) {
        self.push(T::default());
    }
}
