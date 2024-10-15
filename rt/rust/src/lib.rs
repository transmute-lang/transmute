#![deny(improper_ctypes_definitions)]
#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::ffi::CStr;

extern "C" {
    fn println(c_char: *const std::ffi::c_char);
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
pub extern "C" fn free_str_as_box_if_managed(b: Box<Str>) {
    let (header, b) = GcHeader::from_box(b);
    if !header.state.is_managed() {
        Box::leak(b);
    }
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
pub extern "C" fn get_str_from_struct_with_str_as_ref(s: &MyStructWithStr) -> *const Str {
    &s.s as *const Str
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
pub extern "C" fn new_struct_with_string_as_ptr() -> *mut () {
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
pub extern "C" fn print_struct_with_string_as_ref(_s: &MyStructWithString) {
    //println!("{}", s.i);
}

#[no_mangle]
pub extern "C" fn print_struct_with_string_as_ptr(s: *mut ()) {
    let s = unsafe { Box::<MyStructWithString>::from_raw(s.cast()) };
    //println!("{}", b.i);
    Box::leak(s);
}

#[repr(C)]
#[repr(align(16))]
struct GcHeader {
    state: State,
    next: Option<*const GcHeader>,
}

impl GcHeader {
    fn rounded_size() -> usize {
        ((size_of::<Self>() - 1) | 15) + 1
    }

    fn layout_for(layout: Layout) -> Layout {
        Layout::from_size_align(layout.size() + Self::rounded_size(), 16).expect("Layout is valid")
    }

    fn from_ptr<'a, T>(ptr: *const T) -> &'a mut GcHeader {
        Box::leak(unsafe { Box::from_raw(ptr.byte_sub(Self::rounded_size()) as *mut GcHeader) })
    }

    fn from_box<'a, T>(b: Box<T>) -> (&'a mut GcHeader, Box<T>) {
        let ptr = Box::into_raw(b);
        let header = Self::from_ptr(ptr);
        (header, unsafe { Box::from_raw(ptr) })
    }
}

#[derive(Debug, Copy, Clone)]
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
        rp(c"  alloc");
        let base_ptr = System.alloc(GcHeader::layout_for(layout));

        assert!(!base_ptr.is_null());

        let header = &mut *(base_ptr as *mut GcHeader);
        header.state = State::Unmanaged;

        base_ptr.byte_add(GcHeader::rounded_size())
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        rp(c"  dealloc");
        System.dealloc(
            ptr.byte_sub(GcHeader::rounded_size()),
            GcHeader::layout_for(layout),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gc_header_size() {
        assert_eq!(GcHeader::rounded_size() % 16, 0);
    }
}
