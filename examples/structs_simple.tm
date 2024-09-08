struct Struct {
    field: number,
}

let f(n: number): number = {
    let s = Struct {
        field: n * 2,
    };

    s.field = s.field + 1;

    ret s.field;
}
