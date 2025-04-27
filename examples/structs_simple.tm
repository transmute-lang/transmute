use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

struct Struct {
    field: number,
}

let main() = {
    let n = number_parse(list_get(args(), 1));

    let s = Struct {
        field: n * 2,
    };

    s.field = s.field + 1;

    print(s.field);
}
