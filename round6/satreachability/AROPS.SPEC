
# Initially A, B and C have the same unknown value

sourceformula [A=B] and [B=C];

# In the end they have specific values

target [A = 10] and [B = 16] and [C = 42];

# Swap the values of A and B

transition swapAB()
TRUE
{
    A := B;
    B := A;
}

# Swap the values of B and C

transition swapBC()
TRUE
{
    B := C;
    C := B;
}

# Multiply A by 3

transition mul3A()
TRUE
{
    A := A*3;
}

# Add 3 to B

transition add3B()
TRUE
{
    B := B+3;
}

# Deduct 2 from C

transition sub2C()
TRUE
{
    C := C-2;
}
