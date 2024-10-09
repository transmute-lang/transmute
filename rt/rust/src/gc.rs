use std::alloc::{GlobalAlloc, Layout};

#[link(name = "gc")]
extern "C" {
    fn gc_malloc(size: usize) -> *mut u8;
    // fn gc_run();
    fn rust_malloc(size: usize, align: usize);
    fn rust_dealloc(ptr: *const u8, size: usize, align: usize);
}

pub struct GCMalloc {}

impl GCMalloc {
    pub const fn new() -> Self {
        Self {}
    }
}

unsafe impl GlobalAlloc for GCMalloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        rust_malloc(layout.size(), layout.align());
        gc_malloc(layout.size())
        // self.alloc.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        rust_dealloc(ptr.cast_const(), layout.size(), layout.align());
        // gc_run()
        //self.alloc.dealloc(ptr, layout)
    }
}
