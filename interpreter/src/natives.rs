use crate::value::{Ref, Value};
use crate::{Heap, NativeContext, Stack};

pub struct InterpreterNatives<'i> {
    args: &'i [String],
}

impl<'i> InterpreterNatives<'i> {
    pub fn new(args: &'i [String]) -> Self {
        Self { args }
    }
}

impl InterpreterNatives<'_> {
    fn dispatch_boolean(
        &self,
        name: &str,
        parameters: &[Ref],
        _stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match name {
            "print" => {
                let bool = heap.get(parameters[0].0).unwrap().as_bool();
                println!("{bool}");
                None
            }
            _ => {
                panic!("function {} not found on number", name)
            }
        }
    }

    fn dispatch_number(
        &self,
        name: &str,
        parameters: &[Ref],
        _stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match name {
            "print" => {
                let number = heap.get(parameters[0].0).unwrap().as_i64();
                println!("{number}");
                None
            }
            _ => {
                panic!("function {} not found on number", name)
            }
        }
    }

    fn dispatch_string(
        &self,
        name: &str,
        parameters: &[Ref],
        _stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match name {
            "print" => {
                let val = heap.get(parameters[0].0).unwrap().as_str();
                println!("{}", val);
                None
            }
            "number_parse" => {
                let s = heap.get(parameters[0].0).unwrap().as_str();
                let i = s.parse::<i64>().unwrap_or(0);
                heap.push(Value::Number(i));
                Some(Ref(heap.len() - 1))
            }
            _ => {
                panic!("function {} not found on number", name)
            }
        }
    }

    fn dispatch_struct(
        &self,
        name: &str,
        _parameters: &[Ref],
        _stack: &mut Stack,
        _heap: &mut Heap,
    ) -> Option<Ref> {
        panic!("function {} not found on struct", name)
    }

    fn dispatch_array(
        &self,
        name: &str,
        parameters: &[Ref],
        _stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match name {
            "list_get" => {
                let arr = parameters[0];
                let arr = heap.get(arr.0).unwrap().as_array();
                let index = parameters[1];
                let index = heap.get(index.0).unwrap().as_i64() as usize;
                arr.get(index).cloned()
            }
            _ => panic!("function {} not found on array", name),
        }
    }

    fn dispatch_void(
        &self,
        name: &str,
        _parameters: &[Ref],
        _stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match name {
            "args" => {
                // fixme if called multiple time, heap is polluted with new instances
                let mut args = Vec::new();
                for arg in self.args {
                    heap.push(Value::String(arg.clone()));
                    args.push(Ref(heap.len() - 1));
                }
                heap.push(Value::Array(args));
                Some(Ref(heap.len() - 1))
            }
            _ => panic!("function {} not found on void", name),
        }
    }
}

impl NativeContext for InterpreterNatives<'_> {
    fn execute(
        &self,
        name: &str,
        parameters: &[Ref],
        stack: &mut Stack,
        heap: &mut Heap,
    ) -> Option<Ref> {
        match parameters
            .first()
            .map(|p| heap.get(p.0).unwrap())
            .unwrap_or(&Value::Void)
        {
            Value::Boolean(_) => self.dispatch_boolean(name, parameters, stack, heap),
            Value::Number(_) => self.dispatch_number(name, parameters, stack, heap),
            Value::String(_) => self.dispatch_string(name, parameters, stack, heap),
            Value::Struct(_) => self.dispatch_struct(name, parameters, stack, heap),
            Value::Array(_) => self.dispatch_array(name, parameters, stack, heap),
            Value::Void => self.dispatch_void(name, parameters, stack, heap),
        }
    }
}
