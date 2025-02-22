use std::alloc::{GlobalAlloc, Layout};
use std::ptr;
use std::ptr::NonNull;

/// Rust version of the struct defined in `gc.h`.
#[repr(C)]
pub struct GcCallbacks {
    pub mark: Option<extern "C" fn(*mut ())>,
    pub free: Option<extern "C" fn(*mut ())>,
}

pub(crate) struct GcAlloc;

impl GcAlloc {
    pub(crate) const fn new() -> Self {
        Self
    }
}

unsafe impl GlobalAlloc for GcAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let ptr = gc_malloc(layout.size(), layout.align(), ptr::null());
        gc_take_ownership(ptr);
        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        gc_release_ownership(ptr as _);
    }
}

pub(crate) trait Collectable {
    /// Enables the collection of the `Collectable` and its "nested" non-opaque allocations.
    fn enable_collection(&self);

    /// Marks the "nested" non-opaque allocations as reachable
    #[allow(unused_variables)]
    fn mark_recursive(ptr: ObjectPtr<Self>) {
        // nothing
    }

    /// Frees the "nested" opaque allocations
    #[allow(unused_variables)]
    fn free_recursive(ptr: ObjectPtr<Self>) {
        // nothing
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct ObjectPtr<T: ?Sized>(NonNull<T>);

impl<T> ObjectPtr<T> {
    pub(crate) fn from_raw(ptr: *mut T) -> Option<Self> {
        NonNull::new(ptr as _).map(Self)
    }

    pub(crate) fn from_ref(r: &T) -> Self {
        Self::from_raw(r as *const T as _).unwrap()
    }

    pub(crate) fn as_ref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }

    pub(crate) fn as_ref_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut() }
    }

    pub(crate) fn as_raw(&self) -> *mut T {
        self.0.as_ptr()
    }

    pub(crate) fn mark(&self) {
        unsafe {
            gc_mark_managed(self.as_raw() as _);
        }
    }

    pub(crate) fn set_callbacks(&self, callbacks: &GcCallbacks) {
        unsafe {
            gc_set_callbacks(self.as_raw() as _, callbacks);
        }
    }

    pub(crate) fn set_unreachable(&self) {
        unsafe {
            gc_release_ownership(self.as_raw() as _);
        }
    }
}

impl<T: Collectable> ObjectPtr<T> {
    pub(crate) fn leak(t: Box<T>) -> Self {
        t.enable_collection();
        Self(unsafe { NonNull::new_unchecked(Box::leak(t)) })
    }
}

extern "C" {
    fn gc_malloc(data_size: usize, align: usize, callbacks: *const GcCallbacks) -> *mut u8;

    fn gc_take_ownership(ptr: *mut u8);

    fn gc_set_callbacks(ptr: *mut u8, callbacks: *const GcCallbacks);

    fn gc_release_ownership(ptr: *mut u8);

    fn gc_mark_managed(ptr: *mut u8);
}
