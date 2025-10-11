use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

let main() = {
    let n = number_parse(list_get(args(), 1));

    let s = Struct!<number> {
        field: n * 2,
    };

    s.field = s.field + 1;

    print(s.field);
}

struct Struct<T> {
    field: T,
}
