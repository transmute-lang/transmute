
let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    std.numbers.print(n);
    std.booleans.print(n == 0);
    std.str.print("hello, world");
}