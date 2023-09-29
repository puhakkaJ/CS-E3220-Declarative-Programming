
# Source not specified: All state variables are false!

# Target: All bits are 1.

target A(0) and A(1) and A(2) and A(3) and A(4) and A(5) and A(6) and A(7) and A(8) and A(9) and A(10) and A(11) and A(12) and A(13) and A(14) and A(15) and A(16) and A(17) and A(18) and A(19);

# Transitions set one bit to 1.

transition setbit(i : [0,19])
TRUE
{ A(i); }
