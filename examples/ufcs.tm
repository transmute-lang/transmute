
use std.str.string;
use std.env.args;
use std.list.list_get;

let main(){
        1.print();
        0.inc().print();
        n.f();

        MyStruct {
            field: "amazing1"
        }.print1();

        let s = MyStruct {
            field: "amazing2"
        };
        s.print2();
}

let inc(a: number): number {
    a + 1;
}

namespace n {
    let f() {
        "hello, world".print();
    }
}

let print1(s: MyStruct) {
    std.str.print(s.field);
}

let print2(s: MyStruct) {
    s.field.print();
}

struct MyStruct {
    field: string,
}

