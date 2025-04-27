use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

let main() {
    let n = number_parse(list_get(args(), 1));

    let n = if true {
        [ 0, 2, 4, 6, 8, 10, 12, 14, 16, 18 ];
    } else {
        [ 1, 3, 5, 7, 9, 11, 13, 15, 17, 19 ];
    }[n];

    print(n);
}