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
    let s = S {
        f1: 0,
        f2: 1,
    };
    gc_stats();
}