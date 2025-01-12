#[cfg(not(test))]
use crate::gc::BlockHeaderPtr;
use crate::gc::{BlockHeader, Collectable, Gc, State};
#[cfg(not(test))]
use crate::stdout::write_stdout;
#[cfg(not(test))]
use std::io::Write;

#[repr(C)]
pub struct Str {
    ptr: *const u8,
    len: usize,
    cap: usize,
}

impl Str {
    // fn to_string(self) -> String {
    //     self.disable_collection();
    //     unsafe { String::from_raw_parts(self.ptr as *mut u8, self.len, self.cap) }
    // }
}

impl Collectable for Str {
    fn enable_collection(&self) {
        BlockHeader::from_object_ptr(self).state =
            State::Unreachable("str", Some(Str::mark_recursive));
        BlockHeader::from_object_ptr(self.ptr).state = State::Unreachable("str.ptr", None);
    }

    fn mark_recursive(header: &BlockHeader) {
        #[cfg(not(test))]
        write_stdout!(
            "    Str::mark_recursive({})\n",
            BlockHeaderPtr::from(header)
        );
        BlockHeader::from_object_ptr(header.object_ref::<Self>().ptr).mark()
    }

    // fn disable_collection(&self) {
    //     GcHeader::from_object_ptr(self).state = State::Alloc;
    //     GcHeader::from_object_ptr(self.ptr).state = State::Alloc;
    // }
}

impl<S: Into<String>> From<S> for Str {
    fn from(value: S) -> Self {
        #[cfg(not(test))]
        write_stdout!("Str::from(Into<String>)\n");
        let string = value.into();
        Str {
            len: string.len(),
            cap: string.capacity(),
            ptr: string.leak().as_ptr(),
        }
    }
}

// impl Drop for Str {
//     fn drop(&mut self) {
//         if !self.is_collectable() {
//             #[cfg(not(test))]
//             write_stdout!("Str::drop()\n");
//             unsafe {
//                 String::from_raw_parts(self.ptr as *mut u8, self.len, self.cap);
//             }
//         }
//     }
// }

#[no_mangle]
pub extern "C" fn stdlib_string_new() -> *mut Str {
    Gc::new(Str::from("hello, world")).leak()
}
