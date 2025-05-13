use std.numbers.print;

struct Rect {
    height: number,
    width: number,
}

let area(r: Rect): number {
    r.height * r.width;
}

let main(){
    Rect {
        height: 2,
        width: 21
    }.area().print();

    print(
        area(
            Rect {
                height: 2,
                width: 21
            }
        )
    );
}