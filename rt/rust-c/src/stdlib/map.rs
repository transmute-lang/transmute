use crate::gc::{free_recursive, mark_recursive, Collectable, GcCallbacks, ObjectPtr};
use std::collections::HashMap;

type MapKey = *const ();
type MapValue = *const ();

pub struct Map(HashMap<MapKey, MapValue>);

impl Map {
    fn new(map: HashMap<MapKey, MapValue>) -> Self {
        Self(map)
    }
}

static CALLBACKS: GcCallbacks = GcCallbacks {
    mark: Some(mark_recursive::<Map>),
    free: Some(free_recursive::<Map>),
};

impl Collectable for Map {
    fn enable_collection(&self) {
        // the inner map iof the HashMap stays owned, it's destroyed when the `free_recursive`
        // function is called
        let object_ptr = ObjectPtr::from_ref(self);
        object_ptr.set_callbacks(&CALLBACKS);
        object_ptr.set_unreachable();
    }

    fn mark_recursive(ptr: ObjectPtr<Map>) {
        for (k, v) in ptr.as_ref().0.iter() {
            ObjectPtr::<()>::from_raw(*k as _).unwrap().mark();
            ObjectPtr::<()>::from_raw(*v as _).unwrap().mark();
        }
    }

    fn free_recursive(ptr: ObjectPtr<Self>) {
        let _ = Map::from(ptr);
    }
}

impl From<ObjectPtr<Map>> for Map {
    fn from(value: ObjectPtr<Map>) -> Self {
        Map::new(unsafe { Box::from_raw(value.as_raw()) }.0)
    }
}

#[no_mangle]
pub extern "C" fn stdlib_map_new() -> *mut Map {
    let map = Box::new(Map::new(HashMap::new()));
    ObjectPtr::leak(map).as_raw()
}

#[no_mangle]
pub extern "C" fn stdlib_map_insert(map: *mut Map, key: *const (), val: *const ()) {
    let mut map_ptr = ObjectPtr::from_raw(map).unwrap();
    map_ptr.as_ref_mut().0.insert(key, val);
}

#[no_mangle]
pub extern "C" fn stdlib_map_remove(map: *mut Map, key: *const ()) {
    let mut map_ptr = ObjectPtr::from_raw(map).unwrap();
    map_ptr.as_ref_mut().0.remove(&key);
}
