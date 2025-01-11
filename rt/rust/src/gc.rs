use crate::stdout::write_stdout;
use std::alloc::Layout;
use std::fmt::{Display, Formatter};
use std::io::Write;
use std::ptr::NonNull;

pub(crate) trait Collectable {
    fn is_collectable(&self) -> bool {
        GcHeader::from_object_ptr(self).is_collectable()
    }
    fn enable_collection(&self);
    fn disable_collection(&self);
}

/// Like `Box`, but for GC-ed objects
pub(crate) struct Gc<T: ?Sized> {
    object: Box<T>,
}

impl<T> Gc<T>
where
    T: Collectable,
{
    pub fn new(object: T) -> Gc<T> {
        Self::from_box(Box::new(object))
    }

    pub fn from_box(object: Box<T>) -> Self {
        Self { object }
    }

    // pub unsafe fn from_ptr(ptr: *mut T) -> Gc<T> {
    //     Self {
    //         object: Box::from_raw(ptr),
    //     }
    // }

    pub fn into_ptr(self) -> *mut T {
        self.object.enable_collection();
        Box::leak(self.object)
    }

    // pub fn into_box(self) -> Box<T> {
    //     self.object.disable_collection();
    //     self.object
    // }

    // pub fn unwrap(self) -> T {
    //     *self.into_box()
    // }
}

// impl<T> Deref for Gc<T> {
//     type Target = T;
//
//     fn deref(&self) -> &Self::Target {
//         &self.object
//     }
// }
//
// impl<T> DerefMut for Gc<T> {
//     fn deref_mut(&mut self) -> &mut Self::Target {
//         &mut self.object
//     }
// }

// todo move GcHeader to alloc.rs as it makes more sense to be there
/// Holds the metadata associated with an allocated block of memory.
#[repr(C)]
#[repr(align(16))]
pub(crate) struct GcHeader {
    pub state: State,
    pub layout: Layout,
    pub next: Option<GcHeaderPtr>,
}

impl GcHeader {
    pub(crate) const fn rounded_size() -> usize {
        ((size_of::<Self>() - 1) | 15) + 1
    }

    pub(crate) fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(
            layout.size() + GcHeader::rounded_size(),
            layout.align().max(16),
        )
        .expect("Layout is valid")
    }

    /// Build a `GcHeader` from a GC-ed object.
    pub(crate) fn from_gc<T>(gc: &Gc<T>) -> &mut GcHeader {
        Self::from_object_box(&gc.object)
    }

    /// Build a `GcHeader` from a reference to its boxed corresponding payload.
    pub(crate) fn from_object_box<T: ?Sized>(b: &Box<T>) -> &mut GcHeader {
        let b = Box::as_ref(b);
        Self::from_object_ref(b)
    }

    /// Build a `GcHeader` from a reference to its corresponding payload.
    pub(crate) fn from_object_ref<T: ?Sized>(r: &T) -> &mut GcHeader {
        Self::from_object_ptr(r)
    }

    /// Build a `GcHeader` from a pointer to its corresponding payload.
    pub(crate) fn from_object_ptr<'a, T: ?Sized>(ptr: *const T) -> &'a mut GcHeader {
        let head_ptr = unsafe { ptr.byte_sub(Self::rounded_size()) } as *mut GcHeader;
        unsafe { &mut *head_ptr }
    }

    pub(crate) fn from_raw_ptr<'a>(ptr: *mut GcHeader) -> &'a mut GcHeader {
        unsafe { &mut *ptr }
    }

    pub(crate) fn to_gc_header_ptr(&self) -> GcHeaderPtr {
        GcHeaderPtr::from(self)
    }

    pub(crate) fn from_gc_header_ptr<'a>(pointer: GcHeaderPtr) -> &'a Self {
        Self::from_raw_ptr(pointer.raw_ptr() as _)
    }

    pub(crate) fn from_gc_header_ptr_mut<'a>(pointer: GcHeaderPtr) -> &'a mut Self {
        Self::from_raw_ptr(pointer.raw_ptr() as _)
    }

    /// Returns a ref to the object
    pub(crate) fn object_ref<T>(&self) -> &T {
        let ptr = self.object_ptr::<T>();
        unsafe { &*ptr }
    }

    pub(crate) fn object_ptr<T>(&self) -> *const T {
        let ptr = self as *const GcHeader;
        let ptr = unsafe { ptr.byte_add(Self::rounded_size()) };
        ptr as *const T
    }

    pub(crate) fn ptr(&self) -> *const Self {
        self as *const Self
    }

    pub(crate) fn is_collectable(&self) -> bool {
        self.state.is_collectable()
    }

    pub(crate) fn mark(&mut self) {
        #[cfg(not(test))]
        write_stdout!("  mark:{}\n", self.to_gc_header_ptr());
        self.state = match self.state {
            State::Reachable(_) => self.state,
            State::Unreachable(f) => {
                if let Some(f) = f {
                    f(self)
                };
                State::Reachable(f)
            }
            _ => panic!("cannot transition {:?} to reachable", self.state),
        };
    }

    pub(crate) fn unmark(&mut self) {
        self.state = match self.state {
            State::Unreachable(_) => self.state,
            State::Reachable(f) => State::Unreachable(f),
            _ => panic!("cannot transition {:?} to unreachable", self.state),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub(crate) enum State {
    /// The block is under rust de-allocation rules
    Alloc,
    /// The block was dealloc-ed by rust
    Dealloc,
    Reachable(Option<fn(&GcHeader)>),
    Unreachable(Option<fn(&GcHeader)>),
}

impl State {
    fn is_collectable(&self) -> bool {
        match self {
            State::Alloc => false,
            State::Dealloc => false,
            State::Reachable(_) => false,
            State::Unreachable(_) => true,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct GcHeaderPtr(NonNull<GcHeader>);

impl GcHeaderPtr {
    #[deprecated]
    pub(crate) fn to_header<'a>(self) -> &'a GcHeader {
        GcHeader::from_gc_header_ptr(self)
    }

    pub(crate) fn raw_ptr(&self) -> *const GcHeader {
        self.0.as_ptr() as *const GcHeader
    }

    pub(crate) fn from_ptr(ptr: *mut GcHeader) -> Self {
        GcHeader::from_raw_ptr(ptr).to_gc_header_ptr()
    }
}

impl From<&GcHeader> for GcHeaderPtr {
    fn from(value: &GcHeader) -> Self {
        Self(unsafe { NonNull::new_unchecked(value as *const _ as _) })
    }
}

impl Display for GcHeaderPtr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0.as_ptr())
    }
}

unsafe impl Send for GcHeaderPtr {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::alloc::{GlobalAlloc, System};

    #[test]
    fn gc_header_size_mod_16() {
        assert_eq!(GcHeader::rounded_size() % 16, 0);
    }

    #[test]
    fn gc_header_size() {
        assert_eq!(GcHeader::rounded_size(), 48);
    }

    #[test]
    fn gc_header_ptr() {
        let header_ptr = unsafe { System.alloc(Layout::from_size_align(64, 16).unwrap()) };
        assert!(!header_ptr.is_null());

        let data_ptr = unsafe { header_ptr.byte_add(GcHeader::rounded_size()) };

        assert_eq!(header_ptr, unsafe {
            data_ptr.byte_sub(GcHeader::rounded_size())
        });

        let header = GcHeader::from_object_ptr(data_ptr);

        assert_eq!(header as *mut GcHeader as *mut u8, header_ptr);
    }

    #[test]
    fn gc_header_layout() {
        let layout = Layout::for_value("Hello");
        let gc_header_layout = GcHeader::layout_for(layout);
        assert_eq!(gc_header_layout.size(), 5 + GcHeader::rounded_size());
        assert_eq!(gc_header_layout.align(), 16);
    }

    #[test]
    fn gc_header_from_ptr() {
        let string = Box::new("Hello".to_string());
        let string = Box::leak(string);
        let string_ptr = string as *const String;

        let gc_header_from_ptr = GcHeader::from_object_ptr(string_ptr);
        let gc_header_from_ptr_ptr = gc_header_from_ptr as *const GcHeader;

        assert_eq!(
            string_ptr,
            unsafe { gc_header_from_ptr_ptr.byte_add(GcHeader::rounded_size()) }.cast()
        );
        assert_eq!(
            gc_header_from_ptr_ptr,
            unsafe { string_ptr.byte_sub(GcHeader::rounded_size()) }.cast()
        );
    }

    #[test]
    fn gc_header_from_ref() {
        let string = Box::new("Hello".to_string());
        let string = Box::leak(string);
        let string_ptr = string as *const String;

        let gc_header_from_ref = GcHeader::from_object_ref(string) as *mut GcHeader;
        let gc_header_from_ref_ptr = gc_header_from_ref as *const GcHeader;

        assert_eq!(
            string_ptr,
            unsafe { gc_header_from_ref_ptr.byte_add(GcHeader::rounded_size()) }.cast()
        );
        assert_eq!(
            gc_header_from_ref_ptr,
            unsafe { string_ptr.byte_sub(GcHeader::rounded_size()) } as *mut GcHeader
        );
    }

    #[test]
    fn gc_header_from_box() {
        let string = Box::new("Hello".to_string());
        let string_ptr = Box::as_ref(&string) as *const String;

        let gc_header_from_box = GcHeader::from_object_box(&string);
        let gc_header_from_box_ptr = gc_header_from_box as *const GcHeader;

        assert_eq!(
            string_ptr,
            unsafe { gc_header_from_box_ptr.byte_add(GcHeader::rounded_size()) }.cast()
        );
        assert_eq!(
            gc_header_from_box_ptr,
            unsafe { string_ptr.byte_sub(GcHeader::rounded_size()) }.cast()
        );
    }

    #[test]
    fn gc_header_from_ref_and_ptr_and_box_are_equal() {
        let string_box = Box::new("Hello".to_string());
        let string_ref = Box::as_ref(&string_box);
        let string_ptr = string_ref as *const String;

        let gc_header_from_box = GcHeader::from_object_box(&string_box) as *mut GcHeader;
        let gc_header_from_ref = GcHeader::from_object_ref(string_ref) as *mut GcHeader;
        let gc_header_from_ptr = GcHeader::from_object_ptr(string_ptr) as *mut GcHeader;

        assert_eq!(gc_header_from_box, gc_header_from_ref);
        assert_eq!(gc_header_from_box, gc_header_from_ptr);
    }

    #[test]
    fn gc_header_from_ref_and_ptr_and_box_has_unmanaged_state() {
        let string_box = Box::new("Hello".to_string());
        let string_ref = Box::as_ref(&string_box);
        let string_ptr = string_ref as *const String;

        let gc_header = GcHeader::from_object_box(&string_box);
        assert_eq!(gc_header.state, State::Alloc);

        let gc_header = GcHeader::from_object_ref(string_ref);
        assert_eq!(gc_header.state, State::Alloc);

        let gc_header = GcHeader::from_object_ptr(string_ptr);
        assert_eq!(gc_header.state, State::Alloc);
    }
}
