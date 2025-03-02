use crate::gc::{Collectable, GcCallbacks, ObjectPtr};
use core::slice;
use std::hash::{Hash, Hasher};
use transmute_stdlib_macros::{GcCallbacks, MapKeyVTable};

#[repr(C)]
#[derive(GcCallbacks, MapKeyVTable, Eq, Debug)]
pub struct Str {
    ptr: *const u8,
    len: usize,
    cap: usize,
}

impl Hash for Str {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let string = unsafe { String::from_raw_parts(self.ptr as _, self.len, self.cap) };
        string.hash(state);
        string.leak();
    }
}

impl PartialEq<Self> for Str {
    fn eq(&self, other: &Self) -> bool {
        let string = unsafe { String::from_raw_parts(self.ptr as _, self.len, self.cap) };
        let other_string = unsafe { String::from_raw_parts(other.ptr as _, other.len, other.cap) };
        let eq = string.eq(&other_string);
        string.leak();
        other_string.leak();
        eq
    }
}

impl Collectable for Str {
    fn enable_collection(&self) {
        let object_ptr = ObjectPtr::from_ref(self);
        object_ptr.set_callbacks(&CALLBACKS);
        object_ptr.set_unreachable();

        ObjectPtr::<u8>::from_raw(self.ptr as _)
            .unwrap()
            .set_unreachable();
    }

    fn mark_recursive(ptr: ObjectPtr<Str>) {
        ObjectPtr::<u8>::from_raw(ptr.as_ref().ptr as _)
            .unwrap()
            .mark();
    }
}

impl<S: Into<String>> From<S> for Str {
    fn from(value: S) -> Self {
        let string = value.into();
        Str {
            len: string.len(),
            cap: string.capacity(),
            ptr: string.leak().as_ptr(),
        }
    }
}

impl From<&Str> for &str {
    fn from(value: &Str) -> Self {
        let slice = unsafe { slice::from_raw_parts(value.ptr, value.len) };
        unsafe { std::str::from_utf8_unchecked(slice) }
    }
}

#[no_mangle]
pub extern "C" fn tmc_stdlib_string_new(ptr: *const u8, len: usize) -> *mut Str {
    ObjectPtr::leak(Box::new(Str::from(
        String::from_utf8_lossy(unsafe { slice::from_raw_parts(ptr, len) }).to_string(),
    )))
    .as_raw()
}

// todo ideally we want to use this one but stdout between the GC and this function is interleaved.
//   it should not. is it because of the way io::stdout() is initialized?
// #[no_mangle]
// pub extern "C" fn _TM0_5print1s(str: *mut Str) {
//     println!(
//         "{}",
//         Into::<&str>::into(ObjectPtr::from_raw(str).unwrap().as_ref())
//     );
// }
