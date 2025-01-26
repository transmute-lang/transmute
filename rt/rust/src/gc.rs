#[cfg(not(test))]
use crate::stdout::write_stdout;
use std::alloc::Layout;
use std::fmt::{Debug, Display, Formatter};
#[cfg(not(test))]
use std::io::Write;
use std::ptr::NonNull;

pub(crate) trait Collectable {
    /// Enables the collection of the `Collectable` and its "nested" non-opaque allocations.
    fn enable_collection(&self);

    /// Triggers collection on "nested" opaque allocations performed behind the scenes by the
    /// `Collectable`.
    fn collect_opaque(ptr: ObjectPtr<()>);

    /// Marks the "nested" non-opaque allocations as reachable
    fn mark_recursive(ptr: ObjectPtr<()>);
}

// todo add easier way to convert from/to `BlockHeader` and `BlockHeaderPtr`
// todo add easier way to convert from/to `BlockHeader` and `ObjectPtr`
// todo add easier way to convert from/to `BlockHeaderPtr` and `ObjectPtr`
// todo stuff such as the following should be simpler!
//    return Some(BlockHeaderPtr::from(&*Into::<&mut BlockHeader>::into(
//       ObjectPtr::<()>::new(root.as_ptr()).unwrap(),
//    )));
// todo does it make sense to go straight from object ptr to block header ?
//    Into::<&mut BlockHeader>::into(ObjectPtr::new(data1_ptr).unwrap())

// todo move BlockHeader to alloc.rs as it makes more sense to be there
/// Holds the metadata associated with an allocated block of memory.
pub(crate) struct BlockHeader {
    pub state: State,
    pub label: &'static str,
    pub layout: Layout,
    pub next: Option<BlockHeaderPtr>,
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

    pub(crate) fn mark(&mut self) {
        #[cfg(not(test))]
        write_stdout!(
            "  mark:{} ({})\n",
            BlockHeaderPtr::from(&*self),
            ObjectPtr::<()>::from(&*self)
        );
        self.state = match self.state {
            State::Unreachable {
                mark_recursive,
                collect_opaque,
            } => {
                if let Some(mark_recursive) = mark_recursive {
                    mark_recursive(ObjectPtr::<()>::from(&*self))
                };
                State::Reachable {
                    mark_recursive,
                    collect_opaque,
                }
            }
            s => s,
        };
    }

    pub(crate) fn unmark(&mut self) {
        self.state = match self.state {
            State::Reachable {
                mark_recursive,
                collect_opaque,
            } => State::Unreachable {
                mark_recursive,
                collect_opaque,
            },
            s => s,
        }
    }

    pub(crate) fn collect_opaque(&mut self) {
        match self.state {
            State::Unreachable { collect_opaque, .. } => {
                if let Some(collect_opaque) = collect_opaque {
                    collect_opaque(ObjectPtr::<()>::from(&*self));
                }
            }
            _ => {}
        }
    }
}

impl<T> From<ObjectPtr<T>> for &mut BlockHeader {
    fn from(value: ObjectPtr<T>) -> Self {
        let head_ptr =
            unsafe { value.as_ptr().byte_sub(BlockHeader::rounded_size()) } as *mut BlockHeader;
        unsafe { &mut *head_ptr }
    }
}

#[derive(Copy, Clone, PartialEq)]
#[repr(C)]
pub(crate) enum State {
    /// The block is under rust de-allocation rules
    Alloc,
    /// The block was dealloc-ed by rust
    Dealloc,
    Reachable {
        mark_recursive: Option<fn(ObjectPtr<()>)>,
        collect_opaque: Option<fn(ObjectPtr<()>)>,
    },
    Unreachable {
        mark_recursive: Option<fn(ObjectPtr<()>)>,
        collect_opaque: Option<fn(ObjectPtr<()>)>,
    },
}

impl Debug for State {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            State::Alloc => write!(f, "Alloc"),
            State::Dealloc => write!(f, "Dealloc"),
            State::Reachable { .. } => write!(f, "Reachable"),
            State::Unreachable { .. } => write!(f, "Unreachable"),
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub(crate) struct BlockHeaderPtr(NonNull<BlockHeader>);

impl BlockHeaderPtr {
    pub(crate) fn new(ptr: *mut BlockHeader) -> Option<Self> {
        NonNull::new(ptr).map(Self)
    }

    pub(crate) fn block<'a>(self) -> &'a BlockHeader {
        unsafe { self.0.as_ref() }
    }

    pub(crate) fn block_mut<'a>(mut self) -> &'a mut BlockHeader {
        unsafe { self.0.as_mut() }
    }
}

impl From<&BlockHeader> for BlockHeaderPtr {
    fn from(value: &BlockHeader) -> Self {
        Self(unsafe { NonNull::new_unchecked(value as *const _ as _) })
    }
}

impl Display for BlockHeaderPtr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0.as_ptr())
    }
}

unsafe impl Send for BlockHeaderPtr {}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ObjectPtr<T>(NonNull<T>);

impl<T> ObjectPtr<T> {
    // todo: create `new_unchecked()`? (same as `NonNull::new_unchecked()`)
    pub(crate) fn new(ptr: *mut T) -> Option<Self> {
        NonNull::new(ptr).map(Self)
    }

    pub(crate) fn as_box(self) -> Box<T> {
        unsafe { Box::from_raw(self.0.as_ptr()) }
    }

    pub(crate) fn from_ref(r: &T) -> Self {
        Self::new(r as *const T as *mut T).unwrap()
    }

    pub(crate) fn as_ptr(&self) -> *mut T {
        self.0.as_ptr()
    }

    pub(crate) fn as_ref(&self) -> &T {
        unsafe { self.0.as_ref() }
    }

    pub(crate) fn as_ref_mut(&mut self) -> &mut T {
        unsafe { self.0.as_mut() }
    }
}

impl ObjectPtr<()> {
    pub(crate) fn cast<T>(self) -> ObjectPtr<T> {
        ObjectPtr::<T>::new(self.as_ptr() as *mut T).unwrap()
    }
}

impl<T: Collectable> ObjectPtr<T> {
    pub(crate) fn leak(t: Box<T>) -> Self {
        t.enable_collection();
        Self(unsafe { NonNull::new_unchecked(Box::leak(t)) })
    }
}

impl<T> From<&BlockHeader> for ObjectPtr<T> {
    fn from(value: &BlockHeader) -> Self {
        let ptr = value as *const BlockHeader;
        let ptr = unsafe { ptr.byte_add(BlockHeader::rounded_size()) };
        let ptr = ptr as *mut T;
        Self(unsafe { NonNull::new_unchecked(ptr) })
    }
}

impl<T> Display for ObjectPtr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "obj:{:?}", self.0.as_ptr())
    }
}

impl<T> Copy for ObjectPtr<T> {}

impl<T> Clone for ObjectPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

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

        let header = Into::<&mut BlockHeader>::into(ObjectPtr::new(data_ptr).unwrap());

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

        let gc_header_from_ptr =
            Into::<&mut BlockHeader>::into(ObjectPtr::new(string_ptr as *mut String).unwrap());
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
}
