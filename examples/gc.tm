use std.env.args;
use std.list.list_get;
use std.numbers.number_parse;
use std.numbers.print;

struct Point {
    x: number,
    y: number,
}

struct Rect {
    a: Point,
    b: Point,
}

let main() {
    let n = number_parse(list_get(args(), 1));

    let origin = origin();

    let p1 = Point {
        x: n,
        y: n,
    };
    let r1 = Rect {
        a: origin,
        b: p1,
    };
    r1 = Rect {
        a: p1,
        b: p1,
    };

    let a1 = area(r1);

    let p2 = Point {
        x: n * 2,
        y: n * 2,
    };
    let r2 = Rect {
        a: origin,
        b: p2,
    };

    let a2 = area(r2);

    [
        Point {
            x: 1,
            y: 1,
        },
        Point {
            x: 2,
            y: 2,
        },
        Point {
            x: 3,
            y: 3,
        },
    ];

    # trigger gc
    let a = 0;

    print(a1 + a2);
}

let origin(): Point {
    Point {
        x: 0,
        y: 0,
    };
}

let area(r: Rect): number {
    let dx = r.a.x - r.b.x;
    let dy = r.a.y - r.b.y;

    dx * dy;
}
