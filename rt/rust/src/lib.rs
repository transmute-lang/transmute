#![deny(improper_ctypes_definitions)]
#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::ffi::CStr;
use std::ptr;

extern "C" {
    fn println(c_char: *const std::ffi::c_char);
    fn print_alloc(size: usize, align: usize);
    fn print_dealloc(size: usize, align: usize);
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
    let header = GcHeader::from_box(&b);
    if !header.is_managed() {
        Box::leak(b);
        return false;
    }
    true
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_ref(b: &mut Str) -> bool {
    GcHeader::from_ref(&b).is_managed()
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_ptr(b: *mut Str) -> bool {
    GcHeader::from_ptr(b).is_managed()
}

#[no_mangle]
pub extern "C" fn is_managed_str_as_void_ptr(b: *mut ()) -> bool {
    GcHeader::from_ptr(b).is_managed()
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
    next: *const GcHeader,
}

impl GcHeader {
    fn rounded_size() -> usize {
        ((size_of::<Self>() - 1) | 15) + 1
    }

    fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(
            layout.size() + GcHeader::rounded_size(),
            layout.align().max(16),
        )
        .expect("Layout is valid")
    }

    fn from_box<T>(b: &Box<T>) -> &mut GcHeader {
        let b = Box::as_ref(b);
        Self::from_ref(b)
    }

    fn from_ref<T>(r: &T) -> &mut GcHeader {
        Self::from_ptr(*&r)
    }

    fn from_ptr<'a, T>(ptr: *const T) -> &'a mut GcHeader {
        let head_ptr = unsafe { ptr.byte_sub(Self::rounded_size()) } as *mut GcHeader;
        let head_ref = unsafe { &mut *head_ptr };
        head_ref
    }

    fn is_managed(&self) -> bool {
        self.state.is_managed()
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum State {
    Unmanaged,
    Unreachable(fn(*const GcHeader)),
    Reachable(fn(*const GcHeader)),
}

impl State {
    fn is_managed(&self) -> bool {
        match self {
            State::Unmanaged => false,
            _ => true,
        }
    }
}

#[global_allocator]
static ALLOCATOR: GcAlloc = GcAlloc::new();

pub struct GcAlloc {}

impl GcAlloc {
    pub const fn new() -> Self {
        Self {}
    }
}

unsafe impl GlobalAlloc for GcAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let layout = GcHeader::layout_for(layout);
        #[cfg(not(test))]
        print_alloc(layout.size(), layout.align());
        let header_ptr = System.alloc(layout);

        let ptr = header_ptr.byte_add(GcHeader::rounded_size());

        let header = GcHeader::from_ptr(ptr);
        header.state = State::Unmanaged;
        header.next = ptr::null();

        ptr
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        let layout = GcHeader::layout_for(layout);
        #[cfg(not(test))]
        print_dealloc(layout.size(), layout.align());
        System.dealloc(ptr.byte_sub(GcHeader::rounded_size()), layout)
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
        assert_eq!(GcHeader::rounded_size(), 32);
    }

    #[test]
    fn gc_header_ptr() {
        let header_ptr = unsafe { System.alloc(Layout::from_size_align(64, 16).unwrap()) };
        assert!(!header_ptr.is_null());

        let data_ptr = unsafe { header_ptr.byte_add(GcHeader::rounded_size()) };

        assert_eq!(header_ptr, unsafe {
            data_ptr.byte_sub(GcHeader::rounded_size())
        });

        let header = GcHeader::from_ptr(data_ptr);

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

        let gc_header_from_ptr = GcHeader::from_ptr(string_ptr);
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

        let gc_header_from_ref = GcHeader::from_ref(string) as *mut GcHeader;
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

        let gc_header_from_box = GcHeader::from_box(&string);
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

        let gc_header_from_box = GcHeader::from_box(&string_box) as *mut GcHeader;
        let gc_header_from_ref = GcHeader::from_ref(string_ref) as *mut GcHeader;
        let gc_header_from_ptr = GcHeader::from_ptr(string_ptr) as *mut GcHeader;

        assert_eq!(gc_header_from_box, gc_header_from_ref);
        assert_eq!(gc_header_from_box, gc_header_from_ptr);
    }

    #[test]
    fn gc_header_from_ref_and_ptr_and_box_has_unmanaged_state() {
        let string_box = Box::new("Hello".to_string());
        let string_ref = Box::as_ref(&string_box);
        let string_ptr = string_ref as *const String;

        let gc_header = GcHeader::from_box(&string_box);
        assert_eq!(gc_header.state, State::Unmanaged);
        assert_eq!(gc_header.next, ptr::null());

        let gc_header = GcHeader::from_ref(string_ref);
        assert_eq!(gc_header.state, State::Unmanaged);
        assert_eq!(gc_header.next, ptr::null());

        let gc_header = GcHeader::from_ptr(string_ptr);
        assert_eq!(gc_header.state, State::Unmanaged);
        assert_eq!(gc_header.next, ptr::null());
    }

    #[test]
    fn alloc_produces_unmanaged_block() {
        let layout = Layout::from_size_align(1, 1).unwrap();
        let memory = unsafe { GcAlloc::new().alloc(layout) };
        let gc_header = GcHeader::from_ptr(memory);
        assert_eq!(gc_header.state, State::Unmanaged);
        assert_eq!(gc_header.next, ptr::null());
    }
}
