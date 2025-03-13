struct S {
    f1: [number; 2],
    f2: [number; 2],
}

let main() {
    f();
    gc_run();
    gc_stats();
}

let f() {
    let s = S {
        f1: [0, 1],
        f2: [2, 3],
    };
    gc_stats();
}