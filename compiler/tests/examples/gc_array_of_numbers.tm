let main() {
    f();
    gc_run();
    gc_stats();
}

let f() {
    let a = [0, 2, 3];
    gc_stats();
}