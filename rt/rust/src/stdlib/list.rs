#[cfg(not(test))]
use crate::gc::BlockHeaderPtr;
use crate::gc::{BlockHeader, Collectable, Gc, State};
#[cfg(not(test))]
use crate::stdout::write_stdout;
#[cfg(not(test))]
use std::io::Write;
use std::ptr;

type ListItem = *const ();

#[repr(C)]
pub struct List {
    ptr: *const ListItem,
    len: usize,
    cap: usize,
}

// impl List {
//     fn new() -> Self {
//         Self {
//             ptr: ptr::null(),
//             len: 0,
//             cap: 0,
//         }
//     }
//
//     fn mut_ref<'a>(ptr: *mut List) -> &'a mut Self {
//         unsafe { &mut *ptr }
//     }
// }

impl From<Vec<ListItem>> for List {
    fn from(vec: Vec<ListItem>) -> Self {
        List {
            len: vec.len(),
            cap: vec.capacity(),
            ptr: vec.leak().as_ptr(),
        }
    }
}

impl Collectable for List {
    fn enable_collection(&self) {
        BlockHeader::from_object_ptr(self).state =
            State::Unreachable("list", Some(List::mark_recursive));
        if !self.ptr.is_null() && self.ptr != ptr::dangling::<ListItem>() && self.cap > 0 {
            BlockHeader::from_object_ptr(self.ptr).state = State::Unreachable("list.ptr", None);
        }
    }

    fn mark_recursive(header: &BlockHeader) {
        #[cfg(not(test))]
        write_stdout!(
            "    List::mark_recursive({})\n",
            BlockHeaderPtr::from(header)
        );

        let obj = header.object_ref::<Self>();
        if !obj.ptr.is_null() && obj.ptr != ptr::dangling::<ListItem>() && obj.cap > 0 {
            BlockHeader::from_object_ptr(header.object_ref::<Self>().ptr).mark();
            let vec = Vec::from_extern(header.object_ptr_mut::<List>());

            vec.iter().for_each(|item| {
                BlockHeader::from_object_ptr(*item).mark();
            });

            vec.leak();
        }
    }

    // fn disable_collection(&self) {
    //     GcHeader::from_object_ptr(self).state = State::Alloc;
    // }
}

trait ExternRepr<E> {
    fn from_extern(ptr: *mut E) -> Self;
    fn to_new_extern(self) -> *mut E;
    fn update_extern(self, ptr: *mut E);
}

impl ExternRepr<List> for Vec<ListItem> {
    fn from_extern(ptr: *mut List) -> Self {
        unsafe { Vec::from_raw_parts((*ptr).ptr as *mut ListItem, (*ptr).len, (*ptr).cap) }
    }

    fn to_new_extern(self) -> *mut List {
        Gc::new(List::from(self)).leak()
    }

    fn update_extern(self, ptr: *mut List) {
        let mut list = unsafe { Gc::from_raw(ptr) };
        list.len = self.len();
        list.cap = self.capacity();
        list.ptr = self.leak().as_ptr();
        list.leak();
    }
}

#[no_mangle]
pub extern "C" fn stdlib_list_new() -> *mut List {
    Vec::new().to_new_extern()
}

#[no_mangle]
pub extern "C" fn stdlib_list_push(list: *mut List, element: ListItem) {
    let mut vec = Vec::from_extern(list);
    vec.push(element);
    vec.update_extern(list);
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::stdlib::str::stdlib_string_new;
//
//     #[test]
//     fn test_stdlib_list_push() {
//         let list = stdlib_list_new();
//         assert!(matches!(
//             GcHeader::from_object_ptr(list).state,
//             State::Unreachable(_)
//         ));
//
//         let str = stdlib_string_new();
//
//         let list2 = stdlib_list_push(list, str as *const ());
//
//         // assert_eq!(list, list2);
//     }
// }
