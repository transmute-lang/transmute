#[cfg(not(test))]
use crate::gc::BlockHeaderPtr;
use crate::gc::{BlockHeader, Collectable, ObjectPtr, State};
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

impl List {
    fn update(&mut self, vec: Vec<ListItem>) {
        self.len = vec.len();
        self.cap = vec.capacity();
        self.ptr = vec.leak().as_ptr();
        self.enable_collection();
    }
}

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
        let header = Into::<&mut BlockHeader>::into(ObjectPtr::from_ref(self));
        header.label = "list";
        header.state = State::Unreachable {
            mark_recursive: Some(List::mark_recursive),
            collect_opaque: None,
        };

        if !self.ptr.is_null() && self.ptr != ptr::dangling::<ListItem>() && self.cap > 0 {
            let header =
                Into::<&mut BlockHeader>::into(ObjectPtr::new(self.ptr as *mut ListItem).unwrap());
            header.label = "list.ptr";
            header.state = State::Unreachable {
                mark_recursive: None,
                collect_opaque: None,
            };
        }
    }

    fn collect_opaque(_ptr: ObjectPtr<()>) {
        // nothing
    }

    fn mark_recursive(ptr: ObjectPtr<()>) {
        #[cfg(not(test))]
        write_stdout!(
            "    List::mark_recursive({})\n",
            BlockHeaderPtr::from(&*Into::<&mut BlockHeader>::into(ptr))
        );

        let list = ptr.cast::<List>();
        let list = list.as_ref();
        if !list.ptr.is_null() && list.ptr != ptr::dangling::<ListItem>() && list.cap > 0 {
            Into::<&mut BlockHeader>::into(ObjectPtr::new(list.ptr as *mut ListItem).unwrap())
                .mark();

            let vec = Vec::from(list);

            vec.iter().for_each(|item| {
                Into::<&mut BlockHeader>::into(ObjectPtr::new(*item as *mut List).unwrap()).mark();
            });

            vec.leak();
        }
    }
}

impl From<ObjectPtr<List>> for Vec<ListItem> {
    fn from(ptr: ObjectPtr<List>) -> Self {
        Vec::from(ptr.as_ref())
    }
}

impl From<&List> for Vec<ListItem> {
    fn from(list: &List) -> Self {
        unsafe { Vec::from_raw_parts(list.ptr as *mut _, list.len, list.cap) }
    }
}

#[no_mangle]
pub extern "C" fn stdlib_list_new() -> *mut List {
    ObjectPtr::leak(Box::new(List::from(Vec::new()))).as_ptr()
}

#[no_mangle]
pub extern "C" fn stdlib_list_push(list: *mut List, element: ListItem) {
    let mut ptr = ObjectPtr::new(list).unwrap();
    let mut vec = Vec::from(ptr);
    vec.push(element);
    ptr.as_ref_mut().update(vec);
}
