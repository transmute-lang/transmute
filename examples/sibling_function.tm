let main() {
    std.numbers.print(fibo(std.numbers.number_parse(std.list.list_get(std.env.args(), 1))));
}

let fibo(n: number): number {
    if n < 2 {
        ret n;
    }
    fibo(n - 1) + fibo(n - 2);
}