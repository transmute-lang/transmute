struct Vec {
    x: number,
    y: number,
}

let sum(v1: Vec, v2: Vec): Vec = {
    Vec {
        x: v1.x + v2.x,
        y: v1.y + v2.y,
    };
}

let v1 = Vec {
    x: 1,
    y: 1,
};

let v2 = Vec {
    x: 5,
    y: 6,
};

let v3 = sum(v1, v2);

v3.x * v3.y;