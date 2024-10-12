#![deny(improper_ctypes_definitions)]
#![deny(improper_ctypes)]

use crate::Str;
use std::alloc::{GlobalAlloc, Layout};

#[link(name = "gc")]
extern "C" {
    fn gc_malloc(size: usize, align: usize, collectable: bool) -> *mut u8;
    fn gc_set_collectable(ptr: *const u8, collectable: bool, collect_fn: extern "C" fn(*mut u8));
    fn gc_collect(ptr: *const u8);

    fn rust_print(number: u8);
}

pub struct GCMalloc {}

impl GCMalloc {
    pub const fn new() -> Self {
        Self {}
    }
}

unsafe impl GlobalAlloc for GCMalloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        gc_malloc(layout.size(), layout.align(), false)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        rust_print(1);
        gc_collect(ptr.cast_const());
    }
}

pub trait Collectable {
    fn into_collectable(self) -> Box<Self>;

    extern "C" fn collect(s: *mut u8) {
        unsafe { rust_print(3) };
        drop(unsafe { Box::from_raw(s) });
    }
}

impl Collectable for Str<'static> {
    fn into_collectable(self) -> Box<Self> {
        let boxed = Box::new(self);
        unsafe {
            rust_print(2);
            gc_set_collectable(&*boxed as *const Self as *const u8, true, Self::collect)
        };
        boxed
    }
}
