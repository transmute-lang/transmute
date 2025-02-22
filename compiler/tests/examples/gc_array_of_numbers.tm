let main(n: number): number {
    f();
    gc_run();
    gc_stats();
    n;
}

let f() {
    let a = [0, 2, 3];
    gc_stats();
}