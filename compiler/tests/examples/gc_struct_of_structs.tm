struct Outer {
    o1: Inner,
    o2: Inner,
}

struct Inner {
    i1: number,
    i2: number,
}

let main() {
    f();
    gc_run();
    gc_stats();
}

let f() {
    let o = Outer {
        o1: Inner {
            i1: 0,
            i2: 1,
        },
        o2: Inner {
            i1: 2,
            i2: 3,
        },
    };
    gc_stats();
}