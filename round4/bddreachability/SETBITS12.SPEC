
# Source not specified: All state variables are false!

# Target: All bits are 1.

target A(0) and A(1) and A(2) and A(3) and A(4) and A(5) and A(6) and A(7) and A(8) and A(9) and A(10) and A(11);

# Transitions set one bit to 1.

transition setbit(i : [0,11])
TRUE
{ A(i); }
