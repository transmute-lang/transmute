struct Inner {
    field: number,
}

struct Outer {
    inner: Inner,
}

let f(i: number): number {
    f2(i) + f3(i) + f4(i) + f5(i);
}

let f2(i: number): number {
    let inner = Inner {
        field: i
    };
    let outer = Outer {
        inner: inner,
    };
    let inner = outer.inner;
    inner.field;
}

let f3(i: number): number {
     let inner = Inner {
         field: i
     };
     let outer = Outer {
         inner: inner,
     };
     outer.inner.field;
 }

let f4(i: number): number {
    let outer = Outer {
        inner: Inner {
            field: i
        },
    };
    let inner = outer.inner;
    inner.field;
}

let f5(i: number): number {
    let outer = Outer {
        inner: Inner {
            field: i
        },
    };
    outer.inner.field;
}