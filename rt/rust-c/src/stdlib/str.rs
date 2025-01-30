use crate::gc::{mark_recursive, Collectable, MetadataPtr, ObjectPtr};

#[repr(C)]
pub struct Str {
    ptr: *const u8,
    len: usize,
    cap: usize,
}

impl Collectable for Str {
    fn enable_collection(&self) {
        let object_ptr = ObjectPtr::<Str>::from_ref(self);
        object_ptr.set_unreachable();

        ObjectPtr::<u8>::from_raw(self.ptr as _)
            .unwrap()
            .set_unreachable();

        let mut metadata_ptr = MetadataPtr::from_object_ptr(&object_ptr);
        metadata_ptr.as_ref_mut().mark = Some(mark_recursive::<Self>);
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

#[no_mangle]
pub extern "C" fn stdlib_string_new() -> *mut Str {
    let str = Str::from("hello, world");
    let str = Box::new(str);
    ObjectPtr::leak(str).as_raw()
}
