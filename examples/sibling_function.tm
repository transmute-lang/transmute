let main(n: number): number {
    fibo(n);
}

let fibo(n: number): number {
    if n < 2 {
        ret n;
    }
    main(n - 1) + fibo(n - 2);
}