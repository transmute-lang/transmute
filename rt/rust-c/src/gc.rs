use std::alloc::{GlobalAlloc, Layout};
use std::ptr;
use std::ptr::NonNull;

#[repr(C)]
pub(crate) struct Metadata {
    pub mark: Option<extern "C" fn(*mut ())>,
    pub dealloc: Option<extern "C" fn(*mut ())>,
}

impl Metadata {
    pub(crate) const fn rounded_size() -> usize {
        // we want at least size_of(Metadata) + size_of(*Metadata), rounded to the next 16 bytes
        ((size_of::<Self>() + size_of::<*mut Metadata>() - 1) | 15) + 1
    }

    pub(crate) fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(
            layout.size() + Metadata::rounded_size(),
            layout.align().max(16),
        )
        .expect("Layout is valid")
    }
}

pub(crate) struct GcAlloc;

impl GcAlloc {
    pub(crate) const fn new() -> Self {
        Self
    }
}

unsafe impl GlobalAlloc for GcAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let layout = Metadata::layout_for(layout);

        let block_ptr = gc_malloc(layout.size(), layout.align());
        gc_take_ownership(block_ptr);

        if let Some(mut metadata_ptr) = MetadataPtr::from_raw(block_ptr as _) {
            let metadata = metadata_ptr.as_ref_mut();
            metadata.mark = None;
            metadata.dealloc = None;

            {
                // ok, so... the idea is that the last size_of::<*mut u8>() bytes of the metadata
                // block (which is rounded up to the next multiple of 16, see
                // Metadata::rounded_size()) contain a pointer to the beginning of the said metadata
                // block. in order ot ensure we have these last size_of::<*mut u8>() bytes free, we
                // have a field _block_ptr of type *mut u8 inside the Metadata struct.
                let ptr = metadata_ptr.as_raw() as *mut *mut u8;
                let ptr = ptr.byte_add(Metadata::rounded_size()).sub(1);
                *ptr = block_ptr;
            }

            let object_ptr = metadata_ptr.object_ptr().as_raw();
            object_ptr
        } else {
            ptr::null_mut()
        }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let object_ptr = ObjectPtr::from_raw(ptr).unwrap();
        let metadata_ptr = MetadataPtr::from_object_ptr(&object_ptr);
        gc_release_ownership(metadata_ptr.as_raw() as _);
    }
}

pub(crate) trait Collectable {
    /// Enables the collection of the `Collectable` and its "nested" non-opaque allocations.
    fn enable_collection(&self);

    /// Marks the "nested" non-opaque allocations as reachable
    fn mark_recursive(ptr: ObjectPtr<Self>);
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

    pub(crate) fn as_raw(&self) -> *mut T {
        self.0.as_ptr()
    }

    pub(crate) fn mark(&self) {
        unsafe { gc_mark_managed(MetadataPtr::from_object_ptr(self).as_raw() as _) };
    }

    pub(crate) fn set_unreachable(&self) {
        unsafe { gc_release_ownership(MetadataPtr::from_object_ptr(self).as_raw() as _) };
    }
}

impl<T: Collectable> ObjectPtr<T> {
    pub(crate) fn leak(t: Box<T>) -> Self {
        t.enable_collection();
        Self(unsafe { NonNull::new_unchecked(Box::leak(t)) })
    }
}

// impl ObjectPtr<()> {
//     pub(crate) fn cast<T>(self) -> ObjectPtr<T> {
//         ObjectPtr::<T>::from_raw(self.as_raw() as _).unwrap()
//     }
// }

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub(crate) struct MetadataPtr(NonNull<Metadata>);

impl MetadataPtr {
    pub(crate) fn from_raw(ptr: *mut Metadata) -> Option<Self> {
        NonNull::new(ptr as _).map(Self)
    }

    pub(crate) fn from_object_ptr<T>(ptr: &ObjectPtr<T>) -> Self {
        let ptr = unsafe { ptr.as_raw().byte_sub(Metadata::rounded_size()) };
        Self::from_raw(ptr as _).unwrap()
    }

    fn as_raw(self) -> *mut Metadata {
        self.0.as_ptr()
    }

    pub(crate) fn as_ref_mut(&mut self) -> &mut Metadata {
        unsafe { self.0.as_mut() }
    }

    pub(crate) fn object_ptr<T>(&self) -> ObjectPtr<T> {
        let ptr = unsafe { self.as_raw().byte_add(Metadata::rounded_size()) };
        ObjectPtr::from_raw(ptr as _).unwrap()
    }
}

pub extern "C" fn mark_recursive<T: Collectable>(ptr: *mut ()) {
    T::mark_recursive(MetadataPtr::from_raw(ptr as _).unwrap().object_ptr::<T>());
}

extern "C" {
    fn gc_malloc(data_size: usize, align: usize) -> *mut u8;

    fn gc_take_ownership(ptr: *mut u8);

    fn gc_release_ownership(ptr: *mut u8);

    fn gc_mark_managed(ptr: *mut u8);
}

#[cfg(test)]
mod tests {}
