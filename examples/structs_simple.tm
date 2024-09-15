struct Struct {
    field: number,
}

let main(n: number): number = {
    let s = Struct {
        field: n * 2,
    };

    s.field = s.field + 1;

    ret s.field;
}
