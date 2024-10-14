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
pub extern "C" fn free_str_as_box(_: Box<Str>) {
    // nothing
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

#[global_allocator]
static ALLOCATOR: MyAlloc = MyAlloc::new();

pub struct MyAlloc {}

impl MyAlloc {
    pub const fn new() -> Self {
        Self {}
    }
}

unsafe impl GlobalAlloc for MyAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        rp(c"  alloc");
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        rp(c"  dealloc");
        System.dealloc(ptr, layout)
    }
}
