use crate::gc::{Collectable, GcCallbacks, ObjectPtr};
use std::ptr;
use transmute_stdlib_macros::GcCallbacks;

type ListElement = *const ();

#[repr(C)]
#[derive(GcCallbacks)]
pub struct List {
    ptr: *const ListElement,
    len: usize,
    cap: usize,
}

impl List {
    fn update(&mut self, vec: Vec<ListElement>) {
        self.len = vec.len();
        self.cap = vec.capacity();
        self.ptr = vec.leak().as_ptr();
        self.enable_collection();
    }
}

impl From<Vec<ListElement>> for List {
    fn from(vec: Vec<ListElement>) -> Self {
        List {
            len: vec.len(),
            cap: vec.capacity(),
            ptr: vec.leak().as_ptr(),
        }
    }
}

impl Collectable for List {
    fn enable_collection(&self) {
        let object_ptr = ObjectPtr::from_ref(self);
        object_ptr.set_callbacks(&CALLBACKS);
        object_ptr.set_unreachable();

        if !self.ptr.is_null() && self.ptr != ptr::dangling::<ListElement>() && self.cap > 0 {
            ObjectPtr::<u8>::from_raw(self.ptr as _)
                .unwrap()
                .set_unreachable();
        }
    }

    fn mark_recursive(ptr: ObjectPtr<List>) {
        let list = ptr.as_ref();
        if !list.ptr.is_null() && list.ptr != ptr::dangling::<ListElement>() && list.cap > 0 {
            // mark the vector
            ObjectPtr::from_raw(list.ptr as *mut ListElement)
                .unwrap()
                .mark();

            // mark the vector elements
            let vec = Vec::from(list);
            vec.iter()
                .for_each(|element| ObjectPtr::from_raw(*element as *mut ()).unwrap().mark());

            vec.leak();
        }
    }
}

impl From<&List> for Vec<ListElement> {
    fn from(list: &List) -> Self {
        unsafe { Vec::from_raw_parts(list.ptr as *mut _, list.len, list.cap) }
    }
}

#[no_mangle]
pub extern "C" fn stdlib_list_new() -> *mut List {
    let list = List::from(Vec::new());
    let list = Box::new(list);
    ObjectPtr::leak(list).as_raw()
}

#[no_mangle]
pub extern "C" fn stdlib_list_push(list: *mut List, element: ListElement) {
    let mut list_ptr = ObjectPtr::from_raw(list).unwrap();
    let mut vec = Vec::from(list_ptr.as_ref());
    vec.push(element);
    list_ptr.as_ref_mut().update(vec);
}

#[no_mangle]
pub extern "C" fn stdlib_list_pop(list: *mut List) -> ListElement {
    let mut list_ptr = ObjectPtr::from_raw(list).unwrap();
    let mut vec = Vec::from(list_ptr.as_ref());
    let element = vec.pop();
    list_ptr.as_ref_mut().update(vec);
    element.unwrap_or(ptr::null())
}

#[no_mangle]
// list_get(List, number) -> _TM0_8list_get2s4Listn
pub extern "C" fn _TM0_8list_get2s4Listn(list: *const List, index: usize) -> ListElement {
    let list_ptr = ObjectPtr::from_raw(list as *mut List).unwrap();
    let list = Vec::from(list_ptr.as_ref());

    let element = list.get(index).map(|e| e.clone()).unwrap_or(ptr::null());
    list.leak();

    element
}
