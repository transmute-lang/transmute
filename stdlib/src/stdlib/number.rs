use crate::gc::ObjectPtr;
use crate::stdlib::str::Str;

#[no_mangle]
extern "C" fn _TM0_12number_parse1s6string(str: *const Str) -> i64 {
    let str_ptr = ObjectPtr::from_raw(str as *mut Str).unwrap();
    // todo:feature:stdlib should not return i64, but a result<i64, ..>
    Into::<&str>::into(str_ptr.as_ref())
        .parse::<i64>()
        .unwrap_or(0)
}
