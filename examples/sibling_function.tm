let main() {
    print(fibo(number_parse(list_get(args(), 1))));
}

let fibo(n: number): number {
    if n < 2 {
        ret n;
    }
    fibo(n - 1) + fibo(n - 2);
}