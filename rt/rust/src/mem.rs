#![deny(improper_ctypes_definitions)]
#![deny(improper_ctypes)]

use std::alloc::{GlobalAlloc, Layout};
use std::cell::OnceCell;
use std::collections::HashSet;
use std::ops::Deref;
use std::sync::RwLock;

#[link(name = "gc")]
extern "C" {
    fn gc_malloc(size: usize, align: usize, collectable: bool) -> *mut u8;
    fn gc_set_collectable(
        ptr: *const u8,
        collectable: bool,
        collect_fn: Option<extern "C" fn(*mut u8)>,
    );

    pub fn rust_print(what: *const std::ffi::c_char);
}

pub struct GCMalloc {
    statics: OnceCell<RwLock<HashSet<*const u8>>>,
}

impl GCMalloc {
    pub const fn new() -> Self {
        Self {
            statics: OnceCell::new(),
        }
    }

    pub fn add_static(&self, ptr: *const u8) {
        self.statics().write().unwrap().insert(ptr);
    }
    fn statics(&self) -> &RwLock<HashSet<*const u8>> {
        self.statics.get_or_init(|| {
            unsafe { rust_print(c"init statics".as_ptr()) }
            Default::default()
        })
    }

    fn is_static(&self, ptr: *const u8) -> bool {
        self.statics().read().unwrap().contains(&ptr)
    }
}

unsafe impl Sync for GCMalloc {}
unsafe impl Send for GCMalloc {}

unsafe impl GlobalAlloc for GCMalloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        gc_malloc(layout.size(), layout.align(), false)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        if !self.is_static(ptr.cast_const()) {
            rust_print(c"dealloc".as_ptr());
            gc_set_collectable(ptr.cast_const(), true, None)
        }
    }
}

pub trait Collectable {
    extern "C" fn collect(me: *mut u8);

    fn into_collectable(self) -> Box<Self>
    where
        Self: Sized,
    {
        unsafe { rust_print(c"into collectable".as_ptr()) };
        let boxed = Box::new(self);
        unsafe {
            gc_set_collectable(
                &*boxed as *const Self as *const u8,
                true,
                Some(Self::collect),
            )
        };
        boxed
    }

    fn from_collectable(ptr: *mut Self) -> Self
    where
        Self: Sized,
    {
        unsafe {
            rust_print(c"from collectable".as_ptr());
            gc_set_collectable(ptr.cast_const() as *const u8, false, None);
            rust_print(c"from collectable: set collactable false: done".as_ptr());
        }

        let me = unsafe { Box::from_raw(ptr) };

        unsafe { rust_print(c"from collectable: done".as_ptr()) };

        let me = *me;

        unsafe { rust_print(c"from collectable: out of box: done".as_ptr()) };
        todo!();
        me
    }
}
