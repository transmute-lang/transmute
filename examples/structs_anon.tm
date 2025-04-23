struct Struct {
    field: number,
}

let main() = {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let a = Struct {
        field: n,
    }.field;

    std.numbers.print(
        a + Struct {
            field: n
        }.field
    );
}
