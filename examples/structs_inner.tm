#!transmute

struct Point {
    a: number,
}

let area(n: number): number = {
    struct Point {
        x: number,
        y: number,
    }

    let f(a: Point, b: Point): number = {
        (b.x - a.x) * (b.y - a.y);
    }

    f(
        Point {x: 1, y: 1},
        Point {x: n + 7, y: n + 8},
    );
}

let main() {
    std.numbers.print(area(std.numbers.number_parse(std.list.list_get(std.env.args(), 1))));
}
