struct Point {
    x: number,
    y: number,
}

struct Square {
    a: Point,
    b: Point,
}

let perimeter(square: Square): number {
    let width = square.b.x - square.a.x;
    let height = square.b.y - square.a.y;

    ret width * 2 + height * 2;
}

let f(n: number): number = {
    perimeter(
        Square {
            a: Point {
                x: 0,
                y: 0,
            },
            b: Point {
                x: n,
                y: n,
            },
        }
    );
}