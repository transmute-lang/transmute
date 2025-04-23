
let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let a = [ n, 0, n + 2 ];

    a[1] = n + 1;

    std.numbers.print(a[0] + a[0 + 1] + a[1 + 1]);
}