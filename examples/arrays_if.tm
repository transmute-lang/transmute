
let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let n = if true {
        [ 0, 2, 4, 6, 8, 10, 12, 14, 16, 18 ];
    } else {
        [ 1, 3, 5, 7, 9, 11, 13, 15, 17, 19 ];
    }[n];

    std.numbers.print(n);
}