use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;
use std.str.string;
use std.str.print;

let main() = {
    let n = number_parse(list_get(args(), 1));

    let s = Struct {
        str: "Hello",
        num: n * 2,
        #bool: true,
    };

    print(s.num);
    print(s.str);
}

struct Struct {
    num: number,
    # fixme: does not work
    #bool: boolean,
    str: string,
}
