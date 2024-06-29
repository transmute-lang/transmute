
let area() = {
    struct Point {
        x: number,
        y: number,
    }

    let f(a: Point, b: Point): number = {
        (b.x - a.x) * (b.y - a.y);
    }

    f(
        Point {x: 1, y: 1},
        Point {x: 7, y: 8},
    );
}

area();