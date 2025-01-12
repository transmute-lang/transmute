use crate::gc::{BlockHeader, GcHeaderPtr};
use std::ptr::NonNull;

extern "C" {
    fn get_llvm_gc_root_chain() -> *mut LlvmStackFrame;
}

pub fn gc_roots() -> GcRootsIter {
    GcRootsIter {
        current_stack_frame: gc_root(),
        index: 0,
    }
}

pub(crate) struct GcRootsIter {
    current_stack_frame: Option<LlvmStackFrame>,
    index: usize,
}

impl Iterator for GcRootsIter {
    type Item = GcHeaderPtr;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let frame = self.current_stack_frame.as_ref()?;

            match frame.root_nr(self.index) {
                None => {
                    self.index = 0;
                    self.current_stack_frame.replace(frame.next()?);
                }
                Some(root) => {
                    self.index += 1;
                    return Some(BlockHeader::from_object_ptr(root).to_gc_header_ptr());
                }
            }
        }
    }
}

fn gc_root() -> Option<LlvmStackFrame> {
    let ptr = unsafe { get_llvm_gc_root_chain() };
    (!ptr.is_null())
        .then(|| unsafe { NonNull::new_unchecked(ptr) })
        .map(|root| unsafe { root.read_volatile() })
}

#[repr(C)]
struct LlvmStackFrame {
    next: Option<NonNull<LlvmStackFrame>>,
    map: NonNull<LlvmFrameMap>,
    roots: *const (),
}

impl LlvmStackFrame {
    fn num_roots(&self) -> usize {
        unsafe { self.map.read() }.num_roots as usize
    }

    fn root_nr(&self, index: usize) -> Option<*const ()> {
        if index >= self.num_roots() {
            return None;
        }
        Some(unsafe {
            #[allow(clippy::zst_offset)]
            self.roots.add(index)
        })
    }

    fn next(&self) -> Option<LlvmStackFrame> {
        self.next.as_ref().map(|f| unsafe { f.read() })
    }
}

#[repr(C)]
struct LlvmFrameMap {
    num_roots: i32,
    num_meta: i32,
    meta: *const (),
}
