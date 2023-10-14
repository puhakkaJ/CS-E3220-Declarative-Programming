
# A very simple specification with only three state variables

source A,B,C;

target not A and B and C;

transition makeAfalse()
TRUE
{ not A; }
