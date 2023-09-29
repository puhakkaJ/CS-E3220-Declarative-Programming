#!/usr/bin/python3

import sys
from logic import *
from ground import groundmodel
from model2logic import model2logic,transition2logic
from specparser import parseinputfile

#import dd.cudd as _bdd
from dd import autoref as _bdd

def reachability(source,target,transitions,allstatevars):

    # Create a BDD

    bdd = _bdd.BDD()
    # bdd.configure(reordering=True)

    # Names for the current and next state variables

    def CURRENT(v):
        return v
    def NEXT(v):
        return v + "'"

    # All current and next state variables

    oldvars = [ CURRENT(v) for v in allstatevars ]
    newvars = [ NEXT(v) for v in allstatevars ]

    # All variables used in the BDDs

    bddvars = oldvars + newvars

    # Declare BDD variables x and x' for all state variables x

    bdd.declare(*bddvars)

    # Variable orderings

    #  Good ordering has x and x' next to each other

    goodorder = list()
    for v in allstatevars:
        goodorder.extend([CURRENT(v),NEXT(v)])

    #  Bad ordering has all "current" variables before all "next" variables

    badorder = list(allstatevars)
    for v in allstatevars:
        badorder.extend([NEXT(v)])

    # Helper function for turning a list to a dictionary

    def list_to_dict(c):
        return {var: level for level, var in enumerate(c)}

    # Deploy variable ordering (choose either the good or bad ordering here!)

    _bdd.reorder(bdd,list_to_dict(goodorder))
#    _bdd.reorder(bdd,list_to_dict(badorder))

    # Create mappings x => x' and x' => x (needed for image operations)
    
    old2new = {}
    new2old = {}

    for v in allstatevars:
        old2new[CURRENT(v)] = NEXT(v)
        new2old[NEXT(v)] = CURRENT(v)

    # Translate all transitions into logic and further to BDDs

    def trans2logic(t):
        n,c,e = t
        return (n,transition2logic(t,allstatevars)) # Keep name

    transfmas = [ trans2logic(t) for t in transitions ]

    # Translate atoms (x,0) (current value of x)
    # and (x,1) (new value of x) to BDD variables

    def atom4bdd(a):
        x,t = a
        if t == 0:
            return AT(CURRENT(x))
        else:
            return AT(NEXT(x))

    # Build BDD for the target states formula

    targetbdd = target.makeBDD(bdd)

    # Build BDDs for the individual transitions

    print("Constructing BDD for the transition relation")

    transitionbdds = [ (n,f.atommap(atom4bdd).makeBDD(bdd)) for n,f in transfmas ]

    # Build BDD for the relation for all transitions

    transrelation = model2logic(source,target,transitions,allstatevars)
    transbdd = transrelation.atommap(atom4bdd).makeBDD(bdd)

    print("Transition relation completed: size " + str(len(transbdd)))
    
    # Build formula for the initial state.
    # This is either
    #   a formula describing all initial states, or
    #   a list of state variables that are initially true, with
    #   all remaining state variables false.
    # If it is a list, then construct a formula that describes the unique
    # initial state.

    if isinstance(source,list):
        initialfma = CONJ( [ AT(CURRENT(v)) for v in source ] + [ NEG(AT(CURRENT(v))) for v in allstatevars if v not in source ] )
    else:
        initialfma = source

    # Build BDD from the initial state formula

    initialbdd = initialfma.makeBDD(bdd)

    # Symbolic breadth-first search
    
    S = {}
    previousS = bdd.false
    S[0] = initialbdd
    i = 0
    while S[i] != previousS and bdd.apply('and',targetbdd,S[i]) == bdd.false:
        print("Reachability by " + str(i+1) + " transitions: ", end='')
        # All states reachable from S[i] by one step
        newstates = bdd.let(new2old,bdd.exist(oldvars,bdd.apply('and',transbdd,S[i])))
        # Above, bdd.let is for applying the renaming new2old to a BDD,
        #        bdd.exist is for Existential Abstraction
        #        bdd.apply is the Apply operation for doing conjunction/and
        # S[i+1] = S[i] U newstates
        S[i+1] = bdd.apply('or',S[i],newstates)
        print(str(S[i+1].count(nvars = len(allstatevars))) + " states with BDD size " + str(len(S[i+1])))
        previousS = S[i]
        i = i + 1
    # Search ends: target reached, or, all states reached
    if S[i] == previousS:
        print("Target states not reachable")
    else:
        print("Target states reached by " + str(i) + " steps:")
        # Extract transition sequence names
        T = bdd.let(old2new,bdd.apply('and',S[i],targetbdd))
        sequence = []
        while i>0:
            # Find transition from S[i-1] to T
            for nt in transitionbdds:
                n,t = nt
                R = bdd.apply('and',bdd.apply('and',T,t),S[i-1])
                if R != bdd.false:
                    sequence = [n] + sequence
                    T = bdd.let(old2new,bdd.exist(newvars,R))
                    break
            i = i-1
        for s in sequence:
            print(s)

# Main procedure for reading the input file and calling reachability
def main():
    if len(sys.argv) != 2:
        print("Must give exactly one argument [file]")
        exit(1)
    args = sys.argv
    filename = args[1]
    print("Input file: " + filename)
    source,target,transitions = parseinputfile(filename)
    gsource,gtarget,gtransitions,allstatevars = groundmodel(source,target,transitions)
    reachability(gsource,gtarget,gtransitions,allstatevars)

main()
