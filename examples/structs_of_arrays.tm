
struct Point {
    xy: [number; 2],
}

let main() {
    let n = std.numbers.number_parse(std.list.list_get(std.env.args(), 1));

    let p1 = Point {
        xy: [0, 0],
    };
    let p2 = Point {
        xy: [n, n],
    };

    p1.xy[0] = 1;

    let p1xy = p1.xy;
    p1xy[1] = 1;

    let area = (p2.xy[0] - p1xy[0]) * (p2.xy[1] - p1xy[1]);

    std.numbers.print(area);
}