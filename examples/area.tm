#!transmute

struct Square {
    p1: Point,
    p2: Point
}

struct Point {
    x: number,
    y: number
}

let area(s: Square): number = {
    (s.p2.x - s.p1.x) * (s.p2.y - s.p1.y);
}

let p1 = Point {
    x: 1,
    y: 1
};

let p2 = Point {
    x: 6,
    y: 7
};

p2.x = p2.x + 1;
p2.y = p2.y + 1;

area(
    Square {
        p1: p1,
        p2: p2
    }
);