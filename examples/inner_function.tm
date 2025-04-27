use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

let fibo(n: number): number {
    0;
}

let main() {
    let n = number_parse(list_get(args(), 1));

    let fibo(n: number): number {
        if n < 2 {
            ret n;
        }
        fibo(n - 1) + fibo(n - 2);
    }

    print(fibo(n));
}