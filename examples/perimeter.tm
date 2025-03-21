struct Point {
    x: number,
    y: number,
}

struct Square {
    a: Point,
    b: Point,
}

let main() = {
    let n = number_parse(list_get(args(), 1));

    let square = Square {
        a: Point {
            x: 0,
            y: 0,
        },
        b: Point {
            x: n,
            y: n,
        },
    };

    let width = square.b.x - square.a.x;
    let height = square.b.y - square.a.y;

    print(width * 2 + height * 2);
}
