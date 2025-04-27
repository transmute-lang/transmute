use std.booleans.print;
use std.numbers.print;

let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    print(n);
    print(n == 0);
    std.str.print("hello, world");
}