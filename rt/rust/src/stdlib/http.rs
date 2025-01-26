use crate::gc::{BlockHeader, Collectable, ObjectPtr, State};
use crate::stdlib::str::Str;
use reqwest::blocking::Client;

impl Collectable for Client {
    fn enable_collection(&self) {
        Into::<&mut BlockHeader>::into(ObjectPtr::<Client>::from_ref(self)).state =
            State::Unreachable {
                label: "http_client",
                mark_recursive: None,
                collect_opaque: Some(Client::collect_opaque),
            };
    }

    fn collect_opaque(ptr: ObjectPtr<()>) {
        drop(ptr.cast::<Client>().as_box())
    }

    fn mark_recursive(_ptr: ObjectPtr<()>) {}
}

#[no_mangle]
pub extern "C" fn stdlib_http_client_new() -> *mut () {
    ObjectPtr::leak(Box::new(
        reqwest::blocking::ClientBuilder::new().build().unwrap(),
    ))
    .as_ptr()
    .cast()
}

#[no_mangle]
pub extern "C" fn stdlib_http_client_free(http_client: *mut ()) {
    let client = ObjectPtr::new(http_client as *mut Client).unwrap();
    let client = client.as_box();
    drop(client);
}

#[no_mangle]
pub extern "C" fn stdlib_http_client_get(http_client: *mut ()) -> *mut Str {
    let client = ObjectPtr::new(http_client as *mut Client).unwrap();
    let client = client.as_ref();

    let req = client
        .get("https://dummyjson.com/c/3029-d29f-4014-9fb4")
        .build()
        .unwrap();

    let res = client.execute(req).unwrap();
    let str = res.text().unwrap();

    ObjectPtr::leak(Box::new(Str::from(str))).as_ptr()
}
