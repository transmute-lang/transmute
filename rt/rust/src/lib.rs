#![deny(improper_ctypes_definitions)]

mod mem;

use crate::mem::{Collectable, GCMalloc};
use std::ffi::CStr;
use std::marker::PhantomData;

#[global_allocator]
static ALLOCATOR: GCMalloc = GCMalloc::new();

#[no_mangle]
pub extern "C" fn str_new_cstr(cstr: *const std::ffi::c_char) -> Box<Str<'static>> {
    let cstr = unsafe { CStr::from_ptr(cstr) }.to_str().unwrap();

    let a = Box::new(String::with_capacity(1));
    println!("A={a}");

    Str {
        inner: cstr.as_ptr() as *mut u8,
        len: cstr.len(),
        _marker: PhantomData,
    }
    .into_collectable()
}

#[no_mangle]
pub extern "C" fn str_println(s: Box<Str<'static>>) {
    s.println()
}

#[repr(C)]
pub struct Str<'inner> {
    inner: *mut u8,
    len: usize,
    _marker: PhantomData<&'inner ()>,
}

#[no_mangle]
static layout_s3Str: [usize; 2] = [2, 0];

impl<'inner> Str<'inner> {
    fn println(&self) {
        let slice = unsafe { std::slice::from_raw_parts(self.inner, self.len) };
        let str = unsafe { std::str::from_utf8_unchecked(slice) };
        println!("{str}");
    }
}
