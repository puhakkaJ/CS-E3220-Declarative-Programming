
# Movement in a 5 X 5 grid

source at(0,0);

target at(4,4);

transition moveNorth( x : [0,4], y : [0,3] )
at(x,y)
{ not at(x,y); at(x,y+1); }

transition moveSouth( x : [0,4], y : [1,4] )
at(x,y)
{ not at(x,y); at(x,y-1); }

transition moveEast( x : [0,3], y : [0,4] )
at(x,y)
{ not at(x,y); at(x+1,y); }

transition moveWest( x : [1,4], y : [0,4] )
at(x,y)
{ not at(x,y); at(x-1,y); }

# Notice that the numbers only appear as a part of
# the state variable names, and there are no
# numeric state variables: the resulting problem
# instance is purely Boolean, and can be easily
# translated into the propositional logic.
