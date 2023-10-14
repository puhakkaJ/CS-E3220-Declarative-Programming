#!/usr/bin/python3

import sys
from logic2 import *
from ground2 import groundmodel
from model2logic2 import model2logic
from specparser2 import parseinputfile, ParserSyntaxError, LexerReadError

from pysmt.typing import INT
from pysmt.shortcuts import get_model
from pysmt.shortcuts import And
#from pysmt.solvers.solver import get_value

# Test reachability of 'target' from 'source' with 'transitions', by
# at most 'maxN' consecutive transitions.

def satreachability(source,target,trajectory,transitions,allboolvars,allnumvars,maxN):

    # Construct transition relation formula

    transrel0 = model2logic(transitions,allboolvars,allnumvars)
    transrel = transrel0.simplify()

    print("Transition = ",end='')
    print(transrel)

    if trajectory != None:
        print("Trajectory = ",end='')
        print(trajectory)
    else:
        print("Source = ",end='')
        print(source)
        print("Target = ",end='')
        print(target)

    # With trajectory constraint, determine minimum horizon to consider

    if trajectory != None:
        maxTrajTime = 0
        for v in trajectory.vars():
            tokens = v.split("_")
            maxTrajTime = max(maxTrajTime,int(tokens[-1]))
        N = maxTrajTime
    else:
        N = 0

    # N is the index of the last time point, initially N=0 or what is determined by trajectory

    while True:

        # Form a string from a timed atom

        def timedAtom2str(atomtime):
            a,t = atomtime
            return a + "_" + str(t)

        # Instantiate for all time points

        FMAtransitions = []
        for i in range(0,N):
            def shiftTime(atomtime):
                a,t = atomtime
                return (a,t+i)
            FMAtransitions = FMAtransitions + [ transrel.varmap(shiftTime) ]

        # All transition formulas, but all (x,time) turned to strings x_time

        FMA = CONJ([ f.varmap(timedAtom2str) for f in FMAtransitions ] )

        # Turn formulas to SMT, while reducing ATMOST, ATLEAST to plain logic.

        emptySMTstorage()

        # Do we have a trajectory formula? Or use source and target?

        if trajectory == None:
            
            # Source state formula at time point 0

            FMAsource = source.varmap( lambda a : (a,0) )

            # Target state formula at time point N

            FMAtarget = target.varmap( lambda a : (a,N) )

            SMTtrajectory = CONJ([FMAsource,FMAtarget]).varmap(timedAtom2str).makeSMT()
        else:
            SMTtrajectory = trajectory.makeSMT()

        ALLSMT = And([FMA.makeSMT(),SMTtrajectory] + [ f.makeSMT() for f in getSMTstorage() ])

        # Ask SMT solver about satisfiability

        assignment = get_model(ALLSMT)

        # Output satisfying assignment

        if assignment:
            print("SAT " + str(N))
            print(assignment)
            showsolution(assignment,transitions,N,allboolvars,allnumvars)
            break
        else:
            print("UNSAT " + str(N))

        # Increase N, and repeat if below maximum. If no 'target' given,
        # only consider the single horizon length determined by the
        # last time point referred to in the 'trajectory' constraint.

        N = N + 1
        if N >= maxN or target == None:
            break

# Extract transition sequence from a satisfying assignment

def showsolution(assignment,transitions,N,allboolvars,allnumvars):
    print("Transition sequence:")
    # Go from first to last transition in the sequence
    for i in range(0,N):
        # Build states s and s2 at time points i and i+1
        s = {}
        for x in allboolvars:
            s[x] = assignment.get_py_value(Symbol(x + "_" + str(i)))
        for x in allnumvars:
            s[x] = assignment.get_py_value(Symbol(x + "_" + str(i),INT))
        s2 = {}
        for x in allboolvars:
            s2[x] = assignment.get_py_value(Symbol(x + "_" + str(i+1)))
        for x in allnumvars:
            s2[x] = assignment.get_py_value(Symbol(x + "_" + str(i+1),INT))
        # See which transition is between i and i+1
        for t in transitions:
            # Test if transition's condition is true in s
            n,c,e = t
            if not c.eval( lambda v : s[v] ):
                continue
            changesCaused = e.changes( lambda v : s[v] )
            wrong = False
            for x,v in changesCaused:
                if s2[x] != v:
                    wrong = True
            if wrong:
                continue
            # Then check that difference s - s2 is caused by the transition
            differences = { v for v in set.union(allboolvars,allnumvars) if s[v] != s2[v] }
            if not differences.issubset( [ v for v,w in changesCaused ] ):
                continue
            # Condition is true, and effects hold, no other changes
            print(str(i) + ": " + n)
            break

# Main procedure for reading the input file and calling reachability

def main():
    if len(sys.argv) != 2:
        print("Must give exactly one argument [file]")
        exit(1)
    args = sys.argv
    filename = args[1]

    print("Input file: " + filename)

    try:
        source,target,trajectory,transitions = parseinputfile(filename)
    except ParserSyntaxError:
        print("Parser error: exiting...")
        exit(1)
    except LexerReadError:
        print("Lexer error: exiting...")
        exit(1)

    gsource,gtarget,gtrajectory,gtransitions,allboolvars,allnumvars = groundmodel(source,target,trajectory,transitions)

    maxN = 100
    
    satreachability(gsource,gtarget,gtrajectory,gtransitions,allboolvars,allnumvars,maxN)

main()
