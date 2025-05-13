use std.str.print;

let inc(a: number): number {
    a + 1;
}

namespace n {
    let f() {
        print("hello, world");
    }
}

let main(){
        1.inc().print();
        1.print();
        n.f();
}