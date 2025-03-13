struct Struct {
    field: number,
}

let main() = {
    let n = number_parse(list_get(args(), 1));

    let a = Struct {
        field: n,
    }.field;

    print(
        a + Struct {
            field: n
        }.field
    );
}
