use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

let main() {
    let n = number_parse(list_get(args(), 1));

    let a = [ n, 0, n + 2 ];

    a[1] = n + 1;

    print(a[0] + a[0 + 1] + a[1 + 1]);
}