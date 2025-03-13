let main() = {
    let n = number_parse(list_get(args(), 1));

    if n == 0 { print(0); ret; }
    if n == 1 { print(1); ret; }

    let prev_prev = 0;
    let prev = 1;
    let current = 0;

    while n > 1 {
        current = prev_prev + prev;
        prev_prev = prev;
        prev = current;
        n = n - 1;
    }

    print(current);
}
