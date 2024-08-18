#[no_mangle]
pub extern "C" fn rustrt__print__number(number: i64) {
    println!("{number}");
}
