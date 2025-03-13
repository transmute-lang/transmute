
struct Point {
    xy: [number; 2],
}

let main() {
    let n = number_parse(list_get(args(), 1));

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

    print(area);
}