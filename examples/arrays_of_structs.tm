
struct Point {
    x: number,
    y: number,
}

let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let square = [
        Point {
            x: 0,
            y: 0,
        },
        Point {
            x: n,
            y: n,
        },
    ];

    square[0].x = 1;

    let s0 = square[0];
    s0.y = 1;

    let area = (square[1].x - s0.x) * (square[1].y - s0.y);

    std.numbers.print(area);
}