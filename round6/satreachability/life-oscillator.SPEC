
#
# Cellular automata (Game of Life) https://en.wikipedia.org/wiki/Conway%27s_Game_of_Life
#
# A rectangular grid, in which the state of a cell (0 or 1) is determined
# by its neighbors:
#   If cell has 0 or 1 live neighbors, it dies.
#   If cell has 3 live neighbors, it stays or become alive
#   If cell has 4 or more live neighbors, it dies.
#
# Types of interesting patterns in Game of Life:
#   Still life: pattern that stays eternally the same
#   Oscillator: pattern that repeats over a cycle of 2 or more consecutive steps
#   Spacechips: pattern that repeats like an oscillator, but also moves location

xMax=8;
yMax=8;

# Oscillator: pattern that repeats over a cycle of 2 or more consecutive steps
trajectoryformula
   (atleast 1 (x : [0,xMax], y : [0,yMax]) (cell(x,y)@0))
   and (atmost 80 (x : [0,xMax], y : [0,yMax]) (cell(x,y)@1 eqvi cell(x,y)@0))
   and (forall (x : [0,xMax], y : [0,yMax]) (cell(x,y)@0 eqvi cell(x,y)@2));


# Given an initial state, the cellular automaton is deterministic, and
# hence there is only one transition rule. The rule makes the same
# changes for all grid cells: cells with 0 or 1 or over 3 live neighbors die,
# cells with exactly 3 live neighbors become alive.
# Most grid cells have 8 neighbors, but cells in the corners and at edges
# have fewer, and have to be handled separately.

transition lifetransition()
TRUE
{
    # Inner nodes (with 8 neighbors)

    forall (x : [1,xMax-1], y : [1,yMax-1]) {
	if atmost 1 (cell(x-1,y-1),cell(x-1,y),cell(x-1,y+1),cell(x,y-1),cell(x,y+1),cell(x+1,y-1),cell(x+1,y),cell(x+1,y+1)) { not cell(x,y); }
	if atleast 4 (cell(x-1,y-1),cell(x-1,y),cell(x-1,y+1),cell(x,y-1),cell(x,y+1),cell(x+1,y-1),cell(x+1,y),cell(x+1,y+1)) { not cell(x,y); }
	if exactly 3 (cell(x-1,y-1),cell(x-1,y),cell(x-1,y+1),cell(x,y-1),cell(x,y+1),cell(x+1,y-1),cell(x+1,y),cell(x+1,y+1)) { cell(x,y); }
    }

    # Top row (with 5 neighbors)

    forall (x : [1,xMax-1]) {
	if atmost 1 (cell(x-1,0),cell(x-1,1),cell(x,1),cell(x+1,0),cell(x+1,1)) { not cell(x,0); }
	if atleast 4 (cell(x-1,0),cell(x-1,1),cell(x,1),cell(x+1,0),cell(x+1,1)) { not cell(x,0); }
	if exactly 3 (cell(x-1,0),cell(x-1,1),cell(x,1),cell(x+1,0),cell(x+1,1)) { cell(x,0); }
    }

    # Bottom row (with 5 neighbors)

    forall (x : [1,xMax-1]) {
	if atmost 1 (cell(x-1,yMax),cell(x-1,yMax-1),cell(x,yMax-1),cell(x+1,yMax),cell(x+1,yMax-1)) { not cell(x,yMax); }
	if atleast 4 (cell(x-1,yMax),cell(x-1,yMax-1),cell(x,yMax-1),cell(x+1,yMax),cell(x+1,yMax-1)) { not cell(x,yMax); }
	if exactly 3 (cell(x-1,yMax),cell(x-1,yMax-1),cell(x,yMax-1),cell(x+1,yMax),cell(x+1,yMax-1)) { cell(x,yMax); }
    }

    # Left column (with 5 neighbors)

    forall (y : [1,yMax-1]) {
	if atmost 1 (cell(0,y+1),cell(1,y+1),cell(1,y),cell(0,y-1),cell(1,y-1)) { not cell(0,y); }
	if atleast 4 (cell(0,y+1),cell(1,y+1),cell(1,y),cell(0,y-1),cell(1,y-1)) { not cell(0,y); }
	if exactly 3 (cell(0,y+1),cell(1,y+1),cell(1,y),cell(0,y-1),cell(1,y-1)) { cell(0,y); }
    }

    # Right column (with 5 neighbors)

    forall (y : [1,yMax-1]) {
	if atmost 1 (cell(xMax,y-1),cell(xMax-1,y-1),cell(xMax-1,y),cell(xMax,y+1),cell(xMax-1,y+1)) { not cell(xMax,y); }
	if atleast 4 (cell(xMax,y-1),cell(xMax-1,y-1),cell(xMax-1,y),cell(xMax,y+1),cell(xMax-1,y+1)) { not cell(xMax,y); }
	if exactly 3 (cell(xMax,y-1),cell(xMax-1,y-1),cell(xMax-1,y),cell(xMax,y+1),cell(xMax-1,y+1)) { cell(xMax,y); }
    }

    # Upper left corner

    if atmost 1 (cell(1,0),cell(1,1),cell(0,1)) { not cell(0,0); }
    if exactly 3 (cell(1,0),cell(1,1),cell(0,1)) { cell(0,0); }

    # Lower left corner

    if atmost 1 (cell(1,yMax),cell(1,yMax-1),cell(0,yMax-1)) { not cell(0,yMax); }
    if exactly 3 (cell(1,yMax),cell(1,yMax-1),cell(0,yMax-1)) { cell(0,yMax); }

    # Upper right corner

    if atmost 1 (cell(xMax-1,0),cell(xMax-1,1),cell(xMax,1)) { not cell(xMax,0); }
    if exactly 3 (cell(xMax-1,0),cell(xMax-1,1),cell(xMax,1)) { cell(xMax,0); }

    # Lower right corner

    if atmost 1 (cell(xMax-1,yMax),cell(xMax-1,yMax-1),cell(xMax,yMax-1)) { not cell(xMax,yMax); }
    if exactly 3 (cell(xMax-1,yMax),cell(xMax-1,yMax-1),cell(xMax,yMax-1)) { cell(xMax,yMax); }
}
