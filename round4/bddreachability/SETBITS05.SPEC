
#Source not specified: All state variables are false!

#Target: All bits are 1.

target A(0) and A(1) and A(2) and A(3) and A(4);

# Every transition turns one bit 1.

transition setbit(i : [0,4])
TRUE
{ A(i); }
