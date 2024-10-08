let main(n: number): number = {
    if n == 0 { ret 0; }
    if n == 1 { ret 1; }

    let prev_prev = 0;
    let prev = 1;
    let current = 0;

    while n > 1 {
        current = prev_prev + prev;
        prev_prev = prev;
        prev = current;
        n = n - 1;
    }

    current;
}
