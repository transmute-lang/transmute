struct Struct {
    field: number,
}

let main(n: number): number = {
    let a = Struct {
        field: n,
    }.field;

    a + Struct {
        field: n
    }.field;
}
