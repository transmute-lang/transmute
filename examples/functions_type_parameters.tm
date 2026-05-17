use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;
use std.booleans.print;
use std.str.print;

let main() = {
    let n = number_parse(list_get(args(), 1));

    f(Struct!<number> {
        field: n * 2,
    });
}

let f(s: Struct<number>) {
    print(s.field);
}

struct Struct<T> {
    field: T,
}
