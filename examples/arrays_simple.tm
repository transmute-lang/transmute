
let main() {
    let n = number_parse(list_get(args(), 1));

    let a = [ n, 0, n + 2 ];

    a[1] = n + 1;

    print(a[0] + a[0 + 1] + a[1 + 1]);
}