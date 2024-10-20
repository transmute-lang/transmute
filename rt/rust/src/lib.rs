#![deny(improper_ctypes_definitions)]
#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::ffi::CStr;
use std::ptr::NonNull;
use std::sync::Mutex;

extern "C" {
    fn println(c_char: *const std::ffi::c_char);
    fn print_alloc(size: usize, align: usize);
    fn print_dealloc(size: usize, align: usize);
    fn print_ptr(ptr: *const ());
    fn print_update_next_pointer(base: *const (), to: *const ());
    fn print_update_root(to: *const ());
}

fn rp<S: AsRef<CStr>>(s: S) {
    unsafe { println(s.as_ref().as_ptr()) }
}

#[repr(C)]
pub struct Str {
    ptr: *const u8,
    len: usize,
    cap: usize,
}

impl From<String> for Str {
    fn from(value: String) -> Self {
        rp(c"  Str::new()");
        Str {
            len: value.len(),
            cap: value.capacity(),
            ptr: value.leak().as_ptr(),
        }
    }
}

impl From<&str> for Str {
    fn from(value: &str) -> Self {
        Str::from(value.to_string())
    }
}

impl From<Str> for String {
    fn from(value: Str) -> Self {
        unsafe { String::from_raw_parts(value.ptr as *mut u8, value.len, value.cap) }
    }
}

impl Drop for Str {
    fn drop(&mut self) {
        unsafe {
            String::from_raw_parts(self.ptr as *mut u8, self.len, self.cap);
        }
        rp(c"  Str::drop()");
    }
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_box(b: Box<Str>) -> bool {
    let header = GcHeader::from_object_box(&b);
    if !header.is_managed() {
        Box::leak(b);
        return false;
    }
    true
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_ref(b: &mut Str) -> bool {
    GcHeader::from_object_ref(&b).is_managed()
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_ptr(b: *mut Str) -> bool {
    GcHeader::from_object_ptr(b).is_managed()
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_void_ptr(b: *mut ()) -> bool {
    GcHeader::from_object_ptr(b).is_managed()
}

#[repr(C)]
pub struct MyStructWithStr {
    s: Str,
}

impl MyStructWithStr {
    fn new() -> Self {
        rp(c"  MyStructWithStr::new()");
        MyStructWithStr {
            s: Str::from("MyString"),
        }
    }
}

impl Drop for MyStructWithStr {
    fn drop(&mut self) {
        rp(c"  MyStructWithStr::drop()");
    }
}

#[no_mangle]
pub extern "C" fn new_struct_with_str_as_box() -> Box<MyStructWithStr> {
    Box::new(MyStructWithStr::new())
}

#[no_mangle]
pub extern "C" fn free_struct_with_str_as_box(_: Box<MyStructWithStr>) {
    // nothing
}

#[no_mangle]
pub extern "C" fn get_str_from_struct_with_str_as_ref(s: &mut MyStructWithStr) -> *mut Str {
    &mut s.s
}

// #[repr(C)] avoid it to have opaque type on C side
pub struct MyStructWithString {
    i: i32,
    s: String,
}

impl MyStructWithString {
    fn new() -> Self {
        rp(c"  MyStructWithString::new()");
        Self {
            i: 0,
            s: "s".to_string(),
        }
    }
}

impl Drop for MyStructWithString {
    fn drop(&mut self) {
        rp(c"  MyStructWithString::drop()");
    }
}

#[no_mangle]
pub extern "C" fn new_struct_with_string_as_box() -> Box<MyStructWithString> {
    Box::new(MyStructWithString::new())
}

#[no_mangle]
pub extern "C" fn new_struct_with_string_as_void_ptr() -> *mut () {
    let b = Box::new(MyStructWithString::new());
    Box::into_raw(b).cast()
}

#[no_mangle]
pub extern "C" fn new_struct_with_string_as_ptr() -> *mut MyStructWithString {
    let b = Box::new(MyStructWithString::new());
    Box::into_raw(b).cast()
}

#[no_mangle]
pub extern "C" fn free_struct_with_string_as_box(_: Box<MyStructWithString>) {
    // nothing
}

#[no_mangle]
pub extern "C" fn free_struct_with_string_as_ptr(ptr: *mut ()) {
    drop(unsafe { Box::<MyStructWithString>::from_raw(ptr.cast()) });
}

#[no_mangle]
pub extern "C" fn print_struct_with_string_as_box(b: Box<MyStructWithString>) {
    //println!("{}", b.i);
    Box::leak(b);
}

#[no_mangle]
pub extern "C" fn print_struct_with_string_as_ref(_s: &mut MyStructWithString) {
    //println!("{}", s.i);
}

#[no_mangle]
pub extern "C" fn print_struct_with_string_as_ptr(s: *mut ()) {
    let s = unsafe { Box::<MyStructWithString>::from_raw(s.cast()) };
    //println!("{}", b.i);
    Box::leak(s);
}

/// Holds the metadata associated with an allocated block of memory.
#[repr(C)]
#[repr(align(16))]
struct GcHeader {
    state: State,
    layout: Layout,
    next: Option<GcHeaderPtr>,
}

impl GcHeader {
    const fn rounded_size() -> usize {
        ((size_of::<Self>() - 1) | 15) + 1
    }

    fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(
            layout.size() + GcHeader::rounded_size(),
            layout.align().max(16),
        )
        .expect("Layout is valid")
    }

    /// Build a `GcHeader` from a reference to its boxed corresponding payload.
    fn from_object_box<T>(b: &Box<T>) -> &mut GcHeader {
        let b = Box::as_ref(b);
        Self::from_object_ref(b)
    }

    /// Build a `GcHeader` from a reference to its corresponding payload.
    fn from_object_ref<T>(r: &T) -> &mut GcHeader {
        Self::from_object_ptr(r)
    }

    /// Build a `GcHeader` from a pointer to its corresponding payload.
    fn from_object_ptr<'a, T>(ptr: *const T) -> &'a mut GcHeader {
        let head_ptr = unsafe { ptr.byte_sub(Self::rounded_size()) } as *mut GcHeader;
        unsafe { &mut *head_ptr }
    }

    fn from_raw_ptr<'a>(ptr: *mut GcHeader) -> &'a mut GcHeader {
        unsafe { &mut *ptr }
    }

    fn to_pointer(&self) -> GcHeaderPtr {
        GcHeaderPtr::from(self)
    }

    fn from_pointer<'a>(pointer: GcHeaderPtr) -> &'a mut Self {
        Self::from_raw_ptr(pointer.raw_ptr() as _)
    }

    fn is_managed(&self) -> bool {
        self.state.is_managed()
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum State {
    /// The block is under rust de-allocation rules
    Alloc,
    /// The block was dealloc-ed by rust
    Dealloc,
    Unreachable(fn(*const GcHeader)),
    Reachable(fn(*const GcHeader)),
}

impl State {
    fn is_managed(&self) -> bool {
        !matches!(self, State::Alloc)
    }
}

#[global_allocator]
static ALLOCATOR: GcAlloc = GcAlloc::new();

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
struct GcHeaderPtr(NonNull<GcHeader>);

impl GcHeaderPtr {
    fn raw_ptr(&self) -> *const GcHeader {
        self.0.as_ptr() as *const GcHeader
    }
}

impl From<&GcHeader> for GcHeaderPtr {
    fn from(value: &GcHeader) -> Self {
        Self(unsafe { NonNull::new_unchecked(value as *const _ as _) })
    }
}

unsafe impl Send for GcHeaderPtr {}

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
            unsafe { print_ptr(gc_header_ptr.raw_ptr() as _) }
            gc_header_ptr_opt = GcHeader::from_pointer(gc_header_ptr).next;
        }
    }

    fn collect(&self) {
        let mut state = match self.state.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                return;
            }
        };

        let mut prev_gc_header_ptr: Option<GcHeaderPtr> = None;
        let mut gc_header_ptr_opt = state.blocks;

        while let Some(gc_header_ptr) = gc_header_ptr_opt {
            let header = GcHeader::from_pointer(gc_header_ptr);

            if header.state == State::Dealloc {
                if let Some(prev_gc_header_ptr) = prev_gc_header_ptr {
                    GcHeader::from_pointer(prev_gc_header_ptr).next = header.next;
                } else {
                    state.blocks = header.next;
                }

                gc_header_ptr_opt = header.next;

                unsafe {
                    System.dealloc(header as *mut _ as _, header.layout);
                };
            } else {
                prev_gc_header_ptr = Some(gc_header_ptr);
                gc_header_ptr_opt = header.next;
            }
        }
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

unsafe impl GlobalAlloc for GcAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let layout = GcHeader::layout_for(layout);
        let header_ptr = System.alloc(layout);

        let ptr = header_ptr.byte_add(GcHeader::rounded_size());

        let header = GcHeader::from_object_ptr(ptr);
        header.state = State::Alloc;

        let mut state = self.state.lock().unwrap();

        header.next = state.blocks;
        header.layout = layout;

        state.blocks = Some(header.to_pointer());

        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
        let header = GcHeader::from_object_ptr(ptr);

        {
            let _lock = self.state.lock().unwrap();
            header.state = State::Dealloc;
        }

        self.collect();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
