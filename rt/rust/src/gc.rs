#[cfg(not(test))]
use crate::stdout::write_stdout;
use std::alloc::Layout;
use std::fmt::{Display, Formatter};
#[cfg(not(test))]
use std::io::Write;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub(crate) trait Collectable {
    // fn is_collectable(&self) -> bool {
    //     BlockHeader::from_object_ptr(self).is_collectable()
    // }

    fn enable_collection(&self);

    // fn disable_collection(&self);

    fn mark_recursive(header: &BlockHeader);
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
        Self {
            object: Box::new(object),
        }
    }

    pub unsafe fn from_raw(ptr: *mut T) -> Gc<T> {
        Self {
            object: Box::from_raw(ptr),
        }
    }

    pub fn leak(self) -> *mut T {
        self.object.enable_collection();
        Box::leak(self.object)
    }
}

impl<T> Deref for Gc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.object
    }
}

impl<T> DerefMut for Gc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.object
    }
}

// todo move GcHeader to alloc.rs as it makes more sense to be there
/// Holds the metadata associated with an allocated block of memory.
#[repr(C)]
#[repr(align(16))]
pub(crate) struct BlockHeader {
    pub state: State,
    pub layout: Layout,
    pub next: Option<GcHeaderPtr>,
}

impl BlockHeader {
    pub(crate) const fn rounded_size() -> usize {
        ((size_of::<Self>() - 1) | 15) + 1
    }

    pub(crate) fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(
            layout.size() + BlockHeader::rounded_size(),
            layout.align().max(16),
        )
        .expect("Layout is valid")
    }

    // /// Build a `GcHeader` from a GC-ed object.
    // pub(crate) fn from_gc<T>(gc: &Gc<T>) -> &mut BlockHeader {
    //     Self::from_object_box(&gc.object)
    // }

    // /// Build a `GcHeader` from a reference to its boxed corresponding payload.
    // pub(crate) fn from_object_box<T: ?Sized>(b: &Box<T>) -> &mut BlockHeader {
    //     let b = Box::as_ref(b);
    //     Self::from_object_ref(b)
    // }

    // /// Build a `GcHeader` from a reference to its corresponding payload.
    // pub(crate) fn from_object_ref<T: ?Sized>(r: &T) -> &mut BlockHeader {
    //     Self::from_object_ptr(r)
    // }

    /// Build a `GcHeader` from a pointer to its corresponding payload.
    pub(crate) fn from_object_ptr<'a, T: ?Sized>(ptr: *const T) -> &'a mut BlockHeader {
        let head_ptr = unsafe { ptr.byte_sub(Self::rounded_size()) } as *mut BlockHeader;
        unsafe { &mut *head_ptr }
    }

    pub(crate) fn from_raw_ptr<'a>(ptr: *mut BlockHeader) -> &'a mut BlockHeader {
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

    // pub(crate) fn object_ref_mut<T>(&self) -> &mut T {
    //     let ptr = self.object_ptr_mut::<T>();
    //     unsafe { &mut *ptr }
    // }

    pub(crate) fn object_ptr<T>(&self) -> *const T {
        let ptr = self as *const BlockHeader;
        let ptr = unsafe { ptr.byte_add(Self::rounded_size()) };
        ptr as *const T
    }

    pub(crate) fn object_ptr_mut<T>(&self) -> *mut T {
        let ptr = self as *const BlockHeader;
        let ptr = unsafe { ptr.byte_add(Self::rounded_size()) };
        ptr as *mut T
    }

    // pub(crate) fn ptr(&self) -> *const Self {
    //     self as *const Self
    // }

    // pub(crate) fn is_collectable(&self) -> bool {
    //     self.state.is_collectable()
    // }

    pub(crate) fn mark(&mut self) {
        #[cfg(not(test))]
        write_stdout!(
            "  mark:{} (obj:{:?})\n",
            self.to_gc_header_ptr(),
            self.object_ptr::<()>()
        );
        self.state = match self.state {
            State::Reachable(..) => self.state,
            State::Unreachable(s, f) => {
                if let Some(f) = f {
                    f(self)
                };
                State::Reachable(s, f)
            }
            _ => panic!("cannot transition {:?} to reachable", self.state),
        };
    }

    pub(crate) fn unmark(&mut self) {
        self.state = match self.state {
            State::Unreachable(..) => self.state,
            State::Reachable(s, f) => State::Unreachable(s, f),
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
    Reachable(&'static str, Option<fn(&BlockHeader)>),
    Unreachable(&'static str, Option<fn(&BlockHeader)>),
}

// impl State {
//     fn is_collectable(&self) -> bool {
//         match self {
//             State::Alloc => false,
//             State::Dealloc => false,
//             State::Reachable(..) => false,
//             State::Unreachable(..) => true,
//         }
//     }
// }

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct GcHeaderPtr(NonNull<BlockHeader>);

impl GcHeaderPtr {
    // #[deprecated]
    // pub(crate) fn to_header<'a>(self) -> &'a BlockHeader {
    //     BlockHeader::from_gc_header_ptr(self)
    // }

    pub(crate) fn raw_ptr(&self) -> *const BlockHeader {
        self.0.as_ptr() as *const BlockHeader
    }

    // pub(crate) fn from_ptr(ptr: *mut BlockHeader) -> Self {
    //     BlockHeader::from_raw_ptr(ptr).to_gc_header_ptr()
    // }
}

impl From<&BlockHeader> for GcHeaderPtr {
    fn from(value: &BlockHeader) -> Self {
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
        assert_eq!(BlockHeader::rounded_size() % 16, 0);
    }

    #[test]
    fn gc_header_size() {
        assert_eq!(BlockHeader::rounded_size(), 64);
    }

    #[test]
    fn gc_header_ptr() {
        let header_ptr = unsafe { System.alloc(Layout::from_size_align(64, 16).unwrap()) };
        assert!(!header_ptr.is_null());

        let data_ptr = unsafe { header_ptr.byte_add(BlockHeader::rounded_size()) };

        assert_eq!(header_ptr, unsafe {
            data_ptr.byte_sub(BlockHeader::rounded_size())
        });

        let header = BlockHeader::from_object_ptr(data_ptr);

        assert_eq!(header as *mut BlockHeader as *mut u8, header_ptr);
    }

    #[test]
    fn gc_header_layout() {
        let layout = Layout::for_value("Hello");
        let gc_header_layout = BlockHeader::layout_for(layout);
        assert_eq!(gc_header_layout.size(), 5 + BlockHeader::rounded_size());
        assert_eq!(gc_header_layout.align(), 16);
    }

    #[test]
    fn gc_header_from_ptr() {
        let string = Box::new("Hello".to_string());
        let string = Box::leak(string);
        let string_ptr = string as *const String;

        let gc_header_from_ptr = BlockHeader::from_object_ptr(string_ptr);
        let gc_header_from_ptr_ptr = gc_header_from_ptr as *const BlockHeader;

        assert_eq!(
            string_ptr,
            unsafe { gc_header_from_ptr_ptr.byte_add(BlockHeader::rounded_size()) }.cast()
        );
        assert_eq!(
            gc_header_from_ptr_ptr,
            unsafe { string_ptr.byte_sub(BlockHeader::rounded_size()) }.cast()
        );
    }

    // #[test]
    // fn gc_header_from_ref() {
    //     let string = Box::new("Hello".to_string());
    //     let string = Box::leak(string);
    //     let string_ptr = string as *const String;
    //
    //     let gc_header_from_ref = BlockHeader::from_object_ref(string) as *mut BlockHeader;
    //     let gc_header_from_ref_ptr = gc_header_from_ref as *const BlockHeader;
    //
    //     assert_eq!(
    //         string_ptr,
    //         unsafe { gc_header_from_ref_ptr.byte_add(BlockHeader::rounded_size()) }.cast()
    //     );
    //     assert_eq!(gc_header_from_ref_ptr, unsafe {
    //         string_ptr.byte_sub(BlockHeader::rounded_size())
    //     } as *mut BlockHeader);
    // }

    // #[test]
    // fn gc_header_from_box() {
    //     let string = Box::new("Hello".to_string());
    //     let string_ptr = Box::as_ref(&string) as *const String;
    //
    //     let gc_header_from_box = BlockHeader::from_object_box(&string);
    //     let gc_header_from_box_ptr = gc_header_from_box as *const BlockHeader;
    //
    //     assert_eq!(
    //         string_ptr,
    //         unsafe { gc_header_from_box_ptr.byte_add(BlockHeader::rounded_size()) }.cast()
    //     );
    //     assert_eq!(
    //         gc_header_from_box_ptr,
    //         unsafe { string_ptr.byte_sub(BlockHeader::rounded_size()) }.cast()
    //     );
    // }

    // #[test]
    // fn gc_header_from_ref_and_ptr_and_box_are_equal() {
    //     let string_box = Box::new("Hello".to_string());
    //     let string_ref = Box::as_ref(&string_box);
    //     let string_ptr = string_ref as *const String;
    //
    //     let gc_header_from_box = BlockHeader::from_object_box(&string_box) as *mut BlockHeader;
    //     let gc_header_from_ref = BlockHeader::from_object_ref(string_ref) as *mut BlockHeader;
    //     let gc_header_from_ptr = BlockHeader::from_object_ptr(string_ptr) as *mut BlockHeader;
    //
    //     assert_eq!(gc_header_from_box, gc_header_from_ref);
    //     assert_eq!(gc_header_from_box, gc_header_from_ptr);
    // }

    // #[test]
    // fn gc_header_from_ref_and_ptr_and_box_has_unmanaged_state() {
    //     let string_box = Box::new("Hello".to_string());
    //     let string_ref = Box::as_ref(&string_box);
    //     let string_ptr = string_ref as *const String;
    //
    //     let gc_header = BlockHeader::from_object_box(&string_box);
    //     assert_eq!(gc_header.state, State::Alloc);
    //
    //     let gc_header = BlockHeader::from_object_ref(string_ref);
    //     assert_eq!(gc_header.state, State::Alloc);
    //
    //     let gc_header = BlockHeader::from_object_ptr(string_ptr);
    //     assert_eq!(gc_header.state, State::Alloc);
    // }
}
