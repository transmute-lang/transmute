struct Point {
    x: number,
    y: number
}

let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let origin = origin();

    let a = area(origin, Point {
        x: n,
        y: n,
    });

    std.numbers.print(a);
}

let origin(): Point {
    Point {
        x: 0,
        y: 0,
    };
}

let area(p1: Point, p2: Point): number {
    let dx = p2.x - p1.x;
    let dy = p2.y - p1.y;

    dx * dy;
}