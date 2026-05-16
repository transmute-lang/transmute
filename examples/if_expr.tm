#5
use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

let main() {
    let n = number_parse(list_get(args(), 1));

    #let n = if if n == 4 { n+1; } else { n - 1; } >= 5 {
    #    42;
    #} else {
    #    0;
    #};
    let n = if n >= 5 {
        42;
    } else {
        0;
    };

    print(n);
}