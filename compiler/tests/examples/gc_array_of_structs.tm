struct S {
    f1: number,
    f2: number,
}

let main() {
    f();
    gc_run();
    gc_stats();
}

let f() {
    let a = [
        S {
            f1: 0,
            f2: 1,
        },
        S {
            f1: 2,
            f2: 3,
        },
    ];
    gc_stats();
}