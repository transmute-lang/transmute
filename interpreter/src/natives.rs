use crate::value::{Ref, Value};
use crate::{Heap, NativeContext, Stack};

pub struct InterpreterNatives {}

impl InterpreterNatives {
    pub fn new() -> Self {
        Self {}
    }
}

impl InterpreterNatives {
    fn dispatch_boolean(
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
            _ => {
                panic!("function {} not found on number", name)
            }
        }
    }

    fn dispatch_struct(
        name: &str,
        _parameters: &[Ref],
        _stack: &mut Stack,
        _heap: &mut Heap,
    ) -> Option<Ref> {
        panic!("function {} not found on struct", name)
    }

    fn dispatch_array(
        name: &str,
        _parameters: &[Ref],
        _stack: &mut Stack,
        _heap: &mut Heap,
    ) -> Option<Ref> {
        panic!("function {} not found on array", name)
    }

    fn dispatch_void(
        name: &str,
        _parameters: &[Ref],
        _stack: &mut Stack,
        _heap: &mut Heap,
    ) -> Option<Ref> {
        panic!("function {} not found on void", name)
    }
}

impl NativeContext for InterpreterNatives {
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
            Value::Boolean(_) => Self::dispatch_boolean(name, &parameters, stack, heap),
            Value::Number(_) => Self::dispatch_number(name, &parameters, stack, heap),
            Value::String(_) => Self::dispatch_string(name, &parameters, stack, heap),
            Value::Struct(_) => Self::dispatch_struct(name, &parameters, stack, heap),
            Value::Array(_) => Self::dispatch_array(name, &parameters, stack, heap),
            Value::Void => Self::dispatch_void(name, &parameters, stack, heap),
        }
    }
}
