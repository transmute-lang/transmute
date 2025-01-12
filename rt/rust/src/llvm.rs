use crate::gc::{BlockHeader, BlockHeaderPtr};
use std::ptr::NonNull;
use std::slice;

extern "C" {
    fn get_llvm_gc_root_chain() -> *mut LlvmStackFrame;
}

pub fn gc_roots<'frame>() -> GcRootsIter<'frame> {
    GcRootsIter {
        current_stack_frame: gc_root(),
        index: 0,
    }
}

pub(crate) struct GcRootsIter<'frame> {
    current_stack_frame: Option<&'frame LlvmStackFrame>,
    index: usize,
}

impl Iterator for GcRootsIter<'_> {
    type Item = BlockHeaderPtr;

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
                    return Some(BlockHeaderPtr::from(&*BlockHeader::from_object_ptr(
                        root.as_ptr(),
                    )));
                }
            }
        }
    }
}

fn gc_root<'frame>() -> Option<&'frame LlvmStackFrame> {
    let ptr = unsafe { get_llvm_gc_root_chain() };
    (!ptr.is_null()).then(|| unsafe { &*ptr })
}

#[repr(C)]
struct LlvmStackFrame {
    next: Option<NonNull<LlvmStackFrame>>,
    map: NonNull<LlvmFrameMap>,
    roots: NonNull<()>,
}

impl LlvmStackFrame {
    fn num_roots(&self) -> usize {
        unsafe { self.map.as_ref() }.num_roots as usize
    }

    fn root_nr(&self, index: usize) -> Option<NonNull<()>> {
        unsafe { slice::from_raw_parts(&self.roots, self.num_roots()) }
            .get(index)
            .copied()
    }

    fn next<'frame>(&self) -> Option<&'frame LlvmStackFrame> {
        self.next.map(|ptr| unsafe { ptr.as_ref() })
    }
}

#[repr(C)]
struct LlvmFrameMap {
    num_roots: i32,
    num_meta: i32,
    meta: NonNull<()>,
}
