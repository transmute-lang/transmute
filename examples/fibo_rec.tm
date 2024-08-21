let f(n: number): number {
    if n < 2 {
        ret n;
    }
    f(n - 1) + f(n - 2);
}