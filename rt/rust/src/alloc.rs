use crate::gc::{BlockHeaderPtr, ObjectPtr};
use crate::llvm::gc_roots;
use crate::stdout::write_stdout;
use crate::{BlockHeader, State, ALLOCATOR};
use std::alloc::{GlobalAlloc, Layout, System};
use std::io::Write;
use std::ptr;
use std::sync::Mutex;

struct GcAllocState {
    blocks: Option<BlockHeaderPtr>,
    enabled: bool,
}

impl GcAllocState {
    const fn new() -> Self {
        Self {
            blocks: None,
            enabled: true,
        }
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

    fn gc_disable(&self) {
        match self.state.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                write_stdout!("  could not acquire lock\n");
                return;
            }
        }
        .enabled = false;
        #[cfg(not(test))]
        write_stdout!("gc disabled\n");
    }

    fn gc_enable(&self) {
        match self.state.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                write_stdout!("  could not acquire lock\n");
                return;
            }
        }
        .enabled = true;
        #[cfg(not(test))]
        write_stdout!("gc enabled\n");
    }

    fn print_blocks(&self) {
        let mut gc_header_ptr_opt = self.state.lock().unwrap().blocks;
        while let Some(gc_header_ptr) = gc_header_ptr_opt {
            let gc_header = gc_header_ptr.block();
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
        if !state.enabled {
            #[cfg(not(test))]
            write_stdout!("collect() disabled\n");
            return;
        }

        #[cfg(not(test))]
        write_stdout!("collect()\n");

        for root in gc_roots() {
            root.block_mut().mark();
        }

        let mut prev_gc_header_ptr: Option<BlockHeaderPtr> = None;
        let mut gc_header_ptr_opt = state.blocks;

        while let Some(gc_header_ptr) = gc_header_ptr_opt {
            let header = gc_header_ptr.block_mut();

            match header.state {
                State::Dealloc | State::Unreachable(..) => {
                    #[cfg(not(test))]
                    write_stdout!(
                        "  free:{} ({})   {:?}\n",
                        gc_header_ptr,
                        ObjectPtr::<()>::from(&*header),
                        header.state,
                    );

                    if let Some(prev_gc_header_ptr) = prev_gc_header_ptr {
                        #[cfg(not(test))]
                        write_stdout!("    {}.next = {:?}\n", prev_gc_header_ptr, header.next);
                        prev_gc_header_ptr.block_mut().next = header.next;
                    } else {
                        #[cfg(not(test))]
                        write_stdout!("    root.next = {:?}\n", header.next);
                        state.blocks = header.next;
                    }

                    gc_header_ptr_opt = header.next;

                    unsafe {
                        System.dealloc(header as *mut _ as _, header.layout);
                    };
                }
                State::Alloc | State::Reachable(..) => {
                    #[cfg(not(test))]
                    write_stdout!(
                        "  keep:{} ({})   {:?}\n",
                        gc_header_ptr,
                        ObjectPtr::<()>::from(&*header),
                        header.state,
                    );

                    if matches!(header.state, State::Reachable(..)) {
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
        let layout_with_header = BlockHeader::layout_for(layout);

        #[cfg(not(test))]
        write_stdout!(
            "alloc {} bytes ({}, {} bytes aligned)\n",
            layout_with_header.size(),
            layout.size(),
            layout.align(),
        );

        let block_ptr = System.alloc(layout_with_header);

        let header = BlockHeaderPtr::new(block_ptr as *mut BlockHeader)
            .unwrap()
            .block_mut();

        {
            let mut state = self.state.lock().unwrap();
            header.state = State::Alloc;
            header.next = state.blocks;
            header.layout = layout_with_header;

            #[cfg(not(test))]
            write_stdout!("  root.next = {}\n", BlockHeaderPtr::from(&*header));
            state.blocks = Some(BlockHeaderPtr::from(&*header));
        }

        ObjectPtr::<u8>::from(&*header).as_ptr()
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let header = Into::<&mut BlockHeader>::into(ObjectPtr::new(ptr).unwrap());

        #[cfg(not(test))]
        write_stdout!(
            "dealloc {:?} ({} bytes) state: {:?}\n",
            ptr,
            header.layout.size(),
            header.state
        );
        {
            if header.state == State::Alloc {
                header.state = State::Dealloc;
            }
        }

        self.collect();
    }
}

#[no_mangle]
pub extern "C" fn gc_disable() {
    ALLOCATOR.gc_disable();
}

#[no_mangle]
pub extern "C" fn gc_enable() {
    ALLOCATOR.gc_enable();
}

#[no_mangle]
pub extern "C" fn gc_alloc(size: usize, align: usize) -> *mut () {
    let object_ptr = unsafe { ALLOCATOR.alloc(Layout::from_size_align_unchecked(size, align)) };
    let object_ptr = ObjectPtr::new(object_ptr as _).unwrap();

    Into::<&mut BlockHeader>::into(object_ptr).state = State::Unreachable("*", None);

    object_ptr.as_ptr()
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
        while let Some(current_block_ptr) = block_ptr {
            let header = current_block_ptr.block();
            let found = ObjectPtr::<()>::from(header).as_ptr() as *const _ == last;
            block_ptr = header.next;
            if found {
                break;
            }
        }
        block_ptr
    }
    .map(|header| ObjectPtr::<()>::from(header.block()))
    .map(|object| object.as_ptr() as *const _)
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
        let block1_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data).unwrap());
        let block1_ptr = block1_ref as *mut BlockHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(block1_ptr).unwrap()
        );
        assert!(block1_ref.next.is_none());

        let data = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let block2_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data).unwrap());
        let block2_ptr = block2_ref as *mut BlockHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(block2_ptr).unwrap()
        );
        assert_eq!(
            block2_ref.next.unwrap(),
            BlockHeaderPtr::new(block1_ptr).unwrap()
        );
        assert!(block1_ref.next.is_none());

        let data = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let block3_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data).unwrap());
        let block3_ptr = block3_ref as *mut BlockHeader;
        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(block3_ptr).unwrap()
        );
        assert_eq!(
            block3_ref.next.unwrap(),
            BlockHeaderPtr::new(block2_ptr).unwrap()
        );
        assert_eq!(
            block2_ref.next.unwrap(),
            BlockHeaderPtr::new(block1_ptr).unwrap()
        );
        assert!(block1_ref.next.is_none());
    }

    #[test]
    fn gc_free_updates_list_of_gc_headers() {
        let gc_alloc = GcAlloc::new();

        let data1_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let data2_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };
        let data3_ptr = unsafe { gc_alloc.alloc(Layout::from_size_align_unchecked(1, 1)) };

        let header1_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data1_ptr).unwrap());
        let header2_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data2_ptr).unwrap());
        let header3_ref = Into::<&mut BlockHeader>::into(ObjectPtr::new(data3_ptr).unwrap());

        let header1_ptr = header1_ref as *mut BlockHeader;
        let header2_ptr = header2_ref as *mut BlockHeader;
        let header3_ptr = header3_ref as *mut BlockHeader;

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(header3_ptr).unwrap()
        );
        assert_eq!(
            header3_ref.next.unwrap(),
            BlockHeaderPtr::new(header2_ptr).unwrap()
        );
        assert_eq!(
            header2_ref.next.unwrap(),
            BlockHeaderPtr::new(header1_ptr).unwrap()
        );
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data2_ptr, Layout::new::<()>()) };

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(header3_ptr).unwrap()
        );
        assert_eq!(
            header3_ref.next.unwrap(),
            BlockHeaderPtr::new(header1_ptr).unwrap()
        );
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data3_ptr, Layout::new::<()>()) };

        assert_eq!(
            gc_alloc.state.lock().unwrap().blocks.unwrap(),
            BlockHeaderPtr::new(header1_ptr).unwrap()
        );
        assert!(header1_ref.next.is_none());

        unsafe { gc_alloc.dealloc(data1_ptr, Layout::new::<()>()) };
        assert!(gc_alloc.state.lock().unwrap().blocks.is_none());
    }

    #[test]
    fn alloc_produces_unmanaged_block() {
        let layout = Layout::from_size_align(1, 1).unwrap();
        let memory = unsafe { GcAlloc::new().alloc(layout) };
        let gc_header = Into::<&mut BlockHeader>::into(ObjectPtr::new(memory).unwrap());
        assert_eq!(gc_header.state, State::Alloc);
        assert!(gc_header.next.is_none());
    }
}
