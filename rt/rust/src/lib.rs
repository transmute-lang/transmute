#![deny(improper_ctypes_definitions)]

mod mem;

use crate::mem::{rust_print, Collectable, GCMalloc};
use std::collections::HashMap;
use std::ffi::CStr;
use std::marker::PhantomData;

#[global_allocator]
static ALLOCATOR: GCMalloc = GCMalloc::new();

///
/// # Safety
/// Safe under the same conditions as `CStr::from_ptr()`.
#[no_mangle]
pub unsafe extern "C" fn str_new_cstr(cstr: *const std::ffi::c_char) -> Box<Str<'static>> {
    let cstr = unsafe { CStr::from_ptr(cstr) }.to_str().unwrap();

    let a = Box::new(String::with_capacity(1));
    println!("A={a}");

    Str {
        inner: cstr.as_ptr() as *mut u8,
        len: cstr.len(),
        capacity: cstr.len(),
        dropped: false,
        _marker: PhantomData,
    }
    .into_collectable()
}

#[no_mangle]
pub extern "C" fn str_println(s: Box<Str<'_>>) {
    s.println()
}

#[no_mangle]
pub extern "C" fn str_new_static(buf: *mut u8, len: usize, capacity: usize) -> Box<Str<'static>> {
    ALLOCATOR.add_static(buf.cast_const());

    Str {
        inner: buf,
        len,
        capacity,
        dropped: false,
        _marker: PhantomData,
    }
    .into_collectable()
}

#[no_mangle]
pub extern "C" fn outer_add(outer: *mut Outer, s: *mut Str, i: u64) {
    let mut outer = Collectable::from_collectable(outer);
    let string = Collectable::from_collectable(s);
    let string = String::from(string);
    outer.inner.map.insert(string, i);
    std::mem::forget(outer);
}

#[repr(C)]
#[derive(Debug)]
pub struct Str<'inner> {
    inner: *mut u8,
    len: usize,
    capacity: usize,
    dropped: bool,
    _marker: PhantomData<&'inner ()>,
}

impl<'inner> Str<'inner> {
    fn println(&self) {
        let slice = unsafe { std::slice::from_raw_parts(self.inner, self.len) };
        let str = unsafe { std::str::from_utf8_unchecked(slice) };
        println!("{str}");
    }
}

impl Collectable for Str<'_> {
    extern "C" fn collect(s: *mut u8) {
        unsafe { rust_print(c"collect Str".as_ptr()) };
        Collectable::from_collectable(s as *mut Self);
    }
}

impl From<String> for Str<'static> {
    fn from(value: String) -> Self {
        let mut string = value;
        let res = Self {
            inner: string.as_mut_ptr(),
            len: string.len(),
            capacity: string.capacity(),
            dropped: false,
            _marker: PhantomData,
        };
        std::mem::forget(string);
        res
    }
}

// impl Drop for Str<'_> {
//     fn drop(&mut self) {
//         // if !self.dropped {
//         //     self.dropped = true;
//         //     unsafe {
//         //         rust_print(c"drop Str".as_ptr());
//         //         String::from_raw_parts(self.inner, self.len, self.capacity)
//         //     };
//         // }
//     }
// }

impl From<Str<'_>> for String {
    fn from(value: Str<'_>) -> Self {
        unsafe { String::from_raw_parts(value.inner, value.len, value.capacity) }
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct Outer<'inner> {
    inner: Inner<'inner>,
}

#[repr(C)]
#[derive(Debug)]
pub struct Inner<'inner> {
    string: Str<'inner>,
    map: Box<HashMap<String, u64>>,
}

impl Collectable for Inner<'_> {
    extern "C" fn collect(me: *mut u8) {
        todo!()
    }
}

#[no_mangle]
pub extern "C" fn outer_new() -> Box<Outer<'static>> {
    let string = "Hello, world...".to_string();
    Outer {
        inner: Inner {
            string: Str::from(string),
            map: Default::default(),
        },
    }
    .into_collectable()
}

impl Collectable for Outer<'_> {
    extern "C" fn collect(s: *mut u8) {
        unsafe { rust_print(c"collect Outer".as_ptr()) };
        let outer = Self::from_collectable(s as *mut Outer);
        todo!();
        println!("outer: {outer:?}");
        unsafe { rust_print(c"collect Outer: done".as_ptr()) };
        drop(outer);
    }
}
