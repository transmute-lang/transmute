let f(n: number): number {
    if n <= 1 {
        ret n;
    }

    f(n - 1) + f(n - 2);
}

f(9) + 8;