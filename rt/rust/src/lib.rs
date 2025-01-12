#![deny(improper_ctypes_definitions)]
//#![allow(dead_code)]

mod alloc;
mod gc;
mod llvm;
mod stdlib;
mod stdout;

use crate::alloc::GcAlloc;
use crate::gc::{BlockHeader, State};

#[global_allocator]
static ALLOCATOR: GcAlloc = GcAlloc::new();
