#![deny(improper_ctypes_definitions)]

mod gc;

use crate::gc::GCMalloc;
use std::ffi::CStr;
use std::marker::PhantomData;

#[global_allocator]
static ALLOCATOR: GCMalloc = GCMalloc::new();

#[no_mangle]
pub extern "C" fn str_new_cstr(cstr: *const std::ffi::c_char) -> Box<Str<'static>> {
    let cstr = unsafe { CStr::from_ptr(cstr) }.to_str().unwrap();

    let a = Box::new(String::with_capacity(1));

    Box::new(Str {
        inner: cstr.as_ptr(),
        len: cstr.len(),
        _marker: PhantomData,
    })
}

#[repr(C)]
pub struct Str<'inner> {
    inner: *const u8,
    len: usize,
    _marker: PhantomData<&'inner ()>,
}

impl<'inner> Str<'inner> {
    // pub fn from_cstr(cstr: *const std::ffi::c_char) -> Self {
    //     let str = unsafe { CStr::from_ptr(cstr) }.to_str().unwrap();
    // }
    //
    // pub fn from_str(s: &'inner str) -> Self {
    //     Self {
    //         inner: Box::s.as_ptr(),
    //         len: s.len(),
    //         _marker: PhantomData,
    //     }
    // }
    //
    // pub fn as_str(&self) -> &str {
    //     unsafe {
    //         // Note (unsafe): Str can only be created from valid, UTF-8 encoded
    //         // strings by calling `Str::from_str`
    //         std::str::
    //         let s: &[u8] = std::slice::from_raw_parts(self.inner, self.len);
    //         std::str::from_utf8_unchecked(s)
    //     }
    // }
    //
    // pub fn concat(&self, other: &Str<'inner>) -> Str<'inner> {
    //     let mut new_string = String::with_capacity(self.len + other.len);
    //     new_string.push_str(self.as_str());
    //     new_string.push_str(other.as_str());
    //
    //     let new_string = CString::new(new_string).unwrap();
    //
    //     Str {
    //         inner: new_string.as_bytes().as_ptr(),
    //         len: new_string.as_bytes().len(),
    //         _marker: PhantomData,
    //     }
    // }
}
