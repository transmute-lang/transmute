struct Inner {
    field: number,
}

struct Outer {
    field: Inner,
}

let main() {
    let i = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));
    std.numbers.print(f2(i) + f3(i) + f4(i) + f5(i));
}

let f2(i: number): number {
    let inner = Inner {
        field: i
    };
    let outer = Outer {
        field: inner,
    };
    let inner = outer.field;
    inner.field;
}

let f3(i: number): number {
     let inner = Inner {
         field: i
     };
     let outer = Outer {
         field: inner,
     };
     outer.field.field;
 }

let f4(i: number): number {
    let outer = Outer {
        field: Inner {
            field: i
        },
    };
    let inner = outer.field;
    inner.field;
}

let f5(i: number): number {
    let outer = Outer {
        field: Inner {
            field: i
        },
    };
    outer.field.field;
}