let main(n: number): number {
    let fibo(n: number): number {
        if n < 2 {
            ret n;
        }
        main(n - 1) + fibo(n - 2);
    }
    fibo(n);
}