
# Analyze the behavior of a 2-threaded program that swaps
# the values of two integer variables twice.

# 1. TMP[t] = A
# 2. A = B
# 3. B = TMP
# 4.

type THREAD = [0,1];

# A and B have some integer values. OA and OB record the original values.

sourceformula [A=B+5] and [A=OA] and [B=OB] and [PC(0) = 1] and [PC(1) = 1];

# Find out if we can reach a state in which the two thread have
# executed their code until the end, both swapping the values of
# A and B, and the final values differ from the original values.

target [PC(0) = 4] and [PC(1) = 4] and ((not [A = OA]) or (not [B = OB]));

transition line1(t : THREAD)
[PC(t) = 1]
{
    TMP(t) := A;
    PC(t) := 2;
}

transition line2(t : THREAD)
[PC(t) = 2]
{
    A := B;
    PC(t) := 3;
}

transition line3(t : THREAD)
[PC(t) = 3]
{
    B := TMP(t);
    PC(t) := 4;
}
