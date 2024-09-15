struct Struct {
    field: number,
}

let f(n: number): number = {
    let a = Struct {
        field: n,
    }.field;

    a + Struct {
        field: n
    }.field;
}
