
struct Point {
    x: number,
    y: number,
}

let main(n: number): number {
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

    area;
}