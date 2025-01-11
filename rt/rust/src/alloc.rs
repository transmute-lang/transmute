use crate::gc::GcHeaderPtr;
use crate::llvm::gc_roots;
use crate::stdout::write_stdout;
use crate::{GcHeader, State, ALLOCATOR};
use std::alloc::{GlobalAlloc, Layout, System};
use std::io::Write;
use std::ptr;
use std::sync::Mutex;

struct GcAllocState {
    blocks: Option<GcHeaderPtr>,
}

impl GcAllocState {
    const fn new() -> Self {
        Self { blocks: None }
    }
}

pub struct GcAlloc {
    state: Mutex<GcAllocState>,
}

impl GcAlloc {
    #[allow(clippy::new_without_default)] // default is not const
    pub const fn new() -> Self {
        Self {
            state: Mutex::new(GcAllocState::new()),
        }
    }

    fn print_blocks(&self) {
        let mut gc_header_ptr_opt = self.state.lock().unwrap().blocks;
        while let Some(gc_header_ptr) = gc_header_ptr_opt {
            let gc_header = GcHeader::from_gc_header_ptr(gc_header_ptr);
            #[cfg(not(test))]
            {
                write_stdout!("address: {}\n", gc_header_ptr);
                write_stdout!("  size: {} bytes\n", gc_header.layout.size());
                write_stdout!("  state: {:?}\n", gc_header.state);
            }
            gc_header_ptr_opt = gc_header.next;
        }
    }

    fn collect(&self) {
        let mut state = match self.state.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                write_stdout!("  could not acquire lock\n");
                return;
            }
        };

        for root in gc_roots() {
            GcHeader::from_gc_header_ptr_mut(root).mark();
        }

        let mut prev_gc_header_ptr: Option<GcHeaderPtr> = None;
        let mut gc_header_ptr_opt = state.blocks;

        while let Some(gc_header_ptr) = gc_header_ptr_opt {
            let header = GcHeader::from_gc_header_ptr_mut(gc_header_ptr);

            match header.state {
                State::Dealloc | State::Unreachable(_) => {
                    #[cfg(not(test))]
                    write_stdout!("  free:{}   (cause: {:?})\n", gc_header_ptr, header.state,);

                    if let Some(prev_gc_header_ptr) = prev_gc_header_ptr {
                        #[cfg(not(test))]
                        write_stdout!(
                            "    {}.next = {:?}\n",
                            prev_gc_header_ptr,
                            header.next.map(|p| p.raw_ptr()).unwrap_or(ptr::null())
                        );
                        GcHeader::from_gc_header_ptr_mut(prev_gc_header_ptr).next = header.next;
                    } else {
                        #[cfg(not(test))]
                        write_stdout!(
                            "    root.next = {:?}\n",
                            header.next.map(|p| p.raw_ptr()).unwrap_or(ptr::null())
                        );
                        state.blocks = header.next;
                    }

                    gc_header_ptr_opt = header.next;

                    unsafe {
                        System.dealloc(header as *mut _ as _, header.layout);
                    };
                }
                State::Alloc | State::Reachable(_) => {
                    #[cfg(not(test))]
                    write_stdout!("  keep:{}   (cause: {:?})\n", gc_header_ptr, header.state,);

                    if matches!(header.state, State::Reachable(_)) {
                        header.unmark();
                    }

                    prev_gc_header_ptr = Some(gc_header_ptr);
                    gc_header_ptr_opt = header.next;
                }
            }
        }
    }
}

unsafe impl GlobalAlloc for GcAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let layout_with_header = GcHeader::layout_for(layout);

        #[cfg(not(test))]
        write_stdout!(
            "alloc {} bytes ({}, {} bytes aligned)\n",
            layout_with_header.size(),
            layout.size(),
            layout.align(),
        );

        let header_ptr = System.alloc(layout_with_header);

        let header = GcHeader::from_raw_ptr(header_ptr.cast());

        {
            let mut state = self.state.lock().unwrap();
            header.state = State::Alloc;
            header.next = state.blocks;
            header.layout = layout_with_header;

            #[cfg(not(test))]
            write_stdout!("  root.next = {}\n", header.to_gc_header_ptr());
            state.blocks = Some(header.to_gc_header_ptr());
        }

        header.object_ptr::<u8>() as *mut u8
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let header = GcHeader::from_object_ptr(ptr);

        #[cfg(not(test))]
        write_stdout!("dealloc({})\n", header.layout.size());
        {
            let _lock = self.state.lock().unwrap();
            if header.state == State::Alloc {
                header.state = State::Dealloc;
            }
        }

        self.collect();
    }
}

#[no_mangle]
pub extern "C" fn gc_alloc(size: usize, align: usize) -> *mut u8 {
    unsafe { ALLOCATOR.alloc(Layout::from_size_align_unchecked(size, align)) }
}

#[no_mangle]
pub extern "C" fn gc_free(ptr: *mut ()) {
    unsafe { ALLOCATOR.dealloc(ptr as *mut u8, Layout::new::<()>()) }
}

#[no_mangle]
pub extern "C" fn gc_collect() {
    ALLOCATOR.collect();
}

#[no_mangle]
pub extern "C" fn gc_list_blocks() {
    ALLOCATOR.print_blocks()
}

#[no_mangle]
pub extern "C" fn gc_next_object_ptr(last: *const ()) -> *const () {
    let state = ALLOCATOR.state.lock().unwrap();

    if last.is_null() {
        state.blocks
    } else {
        let mut block_ptr = state.blocks;
        while let Some(current_block) = block_ptr {
            let header = GcHeader::from_gc_header_ptr(current_block);
            let found = header.object_ptr() == last;
            block_ptr = header.next;
            if found {
                break;
            }
        }
        block_ptr
    }
    .map(|header| GcHeader::from_gc_header_ptr(header).object_ptr())
    .unwrap_or(ptr::null())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gc_alloc_keeps_list_of_gc_headers() {
        let gc_alloc = GcAlloc::new();

        assert!(gc_alloc.state.lock().unwrap().blocks.is_none());

        let data = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let block1_ref = GcHeader::from_object_ptr(data);
        let block1_ptr = block1_ref as *const GcHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            block1_ptr
        );
        assert!(block1_ref.next.is_none());

        let data = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let block2_ref = GcHeader::from_object_ptr(data);
        let block2_ptr = block2_ref as *const GcHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            block2_ptr
        );
        assert_eq!(block2_ref.next.unwrap().raw_ptr(), block1_ptr);
        assert!(block1_ref.next.is_none());

        let data = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let block3_ref = GcHeader::from_object_ptr(data);
        let block3_ptr = block3_ref as *const GcHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            block3_ptr
        );
        assert_eq!(block3_ref.next.unwrap().raw_ptr(), block2_ptr);
        assert_eq!(block2_ref.next.unwrap().raw_ptr(), block1_ptr);
        assert!(block1_ref.next.is_none());
    }

    #[test]
    fn gc_free_updates_list_of_gc_headers() {
        let gc_alloc = GcAlloc::new();

        let data1_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let data2_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let data3_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };

        let header1_ref = GcHeader::from_object_ptr(data1_ptr);
        let header2_ref = GcHeader::from_object_ptr(data2_ptr);
        let header3_ref = GcHeader::from_object_ptr(data3_ptr);

        let header1_ptr = header1_ref as *const GcHeader;
        let header2_ptr = header2_ref as *const GcHeader;
        let header3_ptr = header3_ref as *const GcHeader;

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            header3_ptr
        );
        assert_eq!(header3_ref.next.unwrap().raw_ptr(), header2_ptr);
        assert_eq!(header2_ref.next.unwrap().raw_ptr(), header1_ptr);
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data2_ptr, Layout::new::<()>()) };

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            header3_ptr
        );
        assert_eq!(header3_ref.next.unwrap().raw_ptr(), header1_ptr);
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data3_ptr, Layout::new::<()>()) };

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap().raw_ptr(),
            header1_ptr
        );
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data1_ptr, Layout::new::<()>()) };
        assert!(gc_alloc.state.lock().unwrap().blocks.is_none());
    }

    #[test]
    fn alloc_produces_unmanaged_block() {
        let layout = Layout::from_size_align(1, 1).unwrap();
        let memory = unsafe { GcAlloc::new().alloc(layout) };
        let gc_header = GcHeader::from_object_ptr(memory);
        assert_eq!(gc_header.state, State::Alloc);
        assert!(gc_header.next.is_none());
    }
}
