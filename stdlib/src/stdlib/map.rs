use crate::gc::{Collectable, GcCallbacks, ObjectPtr};
use std::collections::HashMap;
use std::hash::{Hash, Hasher, RandomState};
use std::ptr;
use transmute_stdlib_macros::GcCallbacks;

type MapValue = *const ();

#[repr(C)]
pub struct MapKey {
    value: *const (),
    vtable: &'static MapKeyVTable,
}

impl Hash for MapKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.vtable.hash)(self.value, state as *mut H as *mut ());
    }
}

impl PartialEq for MapKey {
    fn eq(&self, other: &Self) -> bool {
        (self.vtable.equals)(self.value, other.value)
    }
}

impl Eq for MapKey {}

#[repr(C)]
pub struct MapKeyVTable {
    pub hash: extern "C" fn(*const (), *mut ()),
    pub equals: extern "C" fn(*const (), *const ()) -> bool,
}

#[derive(GcCallbacks)]
pub struct Map(HashMap<MapKey, MapValue>);

impl Map {
    fn new(map: HashMap<MapKey, MapValue>) -> Self {
        Self(map)
    }
}

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
            ObjectPtr::<()>::from_raw(k.value as _).unwrap().mark();
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
    let hasher = RandomState::new();
    let map = Box::new(Map::new(HashMap::with_hasher(hasher)));
    ObjectPtr::leak(map).as_raw()
}

#[no_mangle]
pub extern "C" fn stdlib_map_insert(map: *mut Map, key: MapKey, val: MapValue) -> MapValue {
    let mut map_ptr = ObjectPtr::from_raw(map).unwrap();
    map_ptr
        .as_ref_mut()
        .0
        .insert(key, val)
        .map_or(ptr::null(), |val| val)
}

#[no_mangle]
pub extern "C" fn stdlib_map_get(map: *mut Map, key: MapKey) -> MapValue {
    let mut map_ptr = ObjectPtr::from_raw(map).unwrap();
    map_ptr
        .as_ref_mut()
        .0
        .get(&key)
        .map_or(ptr::null(), |val| *val)
}

#[no_mangle]
pub extern "C" fn stdlib_map_len(map: *mut Map) -> usize {
    ObjectPtr::from_raw(map).unwrap().as_ref_mut().0.len()
}

#[no_mangle]
pub extern "C" fn stdlib_map_remove(map: *mut Map, key: MapKey) -> MapValue {
    let mut map_ptr = ObjectPtr::from_raw(map).unwrap();
    map_ptr
        .as_ref_mut()
        .0
        .remove(&key)
        .map_or(ptr::null(), |val| val)
}
