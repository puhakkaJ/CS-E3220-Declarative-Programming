
# A very simple specification with only one numeric variable

#source A = 1, B = 1;
sourceformula [A + B = 5];

target [A + B = 10];

transition incrementA()
TRUE
{ A := A + 1; }

transition incrementB()
TRUE
{ B := B + 1; }
