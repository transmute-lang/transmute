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
        self.stack.pop();
    }

    pub fn last(&self) -> Option<&T> {
        self.stack.last()
    }

    pub fn root(&self) -> Option<&T> {
        self.stack.first()
    }
}
