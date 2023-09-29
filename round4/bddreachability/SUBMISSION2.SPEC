#Source: p1 = 1

source p1;

#Target: X=1 and Y=1.

target X and Y;

# investigate the behavior of a simple procedural program.

transition p1TOp2() p1 and (not X or not Y) {
    p2; not p1;
}

transition p1TOp5() p1 and X and Y {
    not p1; p5;
}

transition p2TOp3() p2 and not X {
    p3; not p2;
}

transition p2TOp4() p2 and X {
    p4; not p2;
}

transition p3TOp1() p3 and not X {
    not p3; X; p1;
}

transition p4TOp1() p4 and X {
    not p4; Y; p1;
}
