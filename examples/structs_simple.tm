struct Struct {
    field: number,
}

let main() = {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let s = Struct {
        field: n * 2,
    };

    s.field = s.field + 1;

    std.numbers.print(s.field);
}
