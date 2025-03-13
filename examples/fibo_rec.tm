let main() {
    let n = number_parse(
        list_get(
            args(),
            1
        )
    );
    let f = fibo(n);
    print(f);
}

let fibo(n: number): number {
    if n < 2 {
        ret n;
    }
    fibo(n - 1) + fibo(n - 2);
}