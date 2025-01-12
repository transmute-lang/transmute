#[cfg(not(test))]
use crate::gc::BlockHeaderPtr;
use crate::gc::{BlockHeader, Collectable, ObjectPtr, State};
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

impl Collectable for Str {
    fn enable_collection(&self) {
        Into::<&mut BlockHeader>::into(ObjectPtr::<Str>::from_ref(self)).state =
            State::Unreachable("str", Some(Str::mark_recursive));

        Into::<&mut BlockHeader>::into(ObjectPtr::<u8>::new(self.ptr as *mut _).unwrap()).state =
            State::Unreachable("str.ptr", None);
    }

    fn mark_recursive(ptr: ObjectPtr<()>) {
        #[cfg(not(test))]
        write_stdout!(
            "    Str::mark_recursive({})\n",
            BlockHeaderPtr::from(&*Into::<&mut BlockHeader>::into(ptr))
        );

        let ptr = ObjectPtr::<u8>::new(ptr.cast::<Str>().as_ref().ptr as *mut _).unwrap();
        Into::<&mut BlockHeader>::into(ptr).mark();
    }
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

#[no_mangle]
pub extern "C" fn stdlib_string_new() -> *mut Str {
    let str = Str::from("hello, world");
    ObjectPtr::leak(Box::new(str)).as_ref_mut()
}
