#![deny(improper_ctypes_definitions)]
//#![allow(dead_code)]

use crate::gc::GcAlloc;

mod gc;
mod stdlib;

#[global_allocator]
pub(crate) static ALLOCATOR: GcAlloc = GcAlloc::new();
