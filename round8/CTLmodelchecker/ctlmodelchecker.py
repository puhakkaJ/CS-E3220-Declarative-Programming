#!/usr/bin/python3

import sys
from CTLlogic import *
from ground3 import groundmodel
from model2logic3 import model2logic,transition2logic
from specparser3 import parseinputfile

#import dd.cudd as _bdd
from dd import autoref as _bdd

def ctlmodelcheck(source,target,transitions,allvars):

    # Create a BDD with x and x' for all state variables x

    bdd = _bdd.BDD()
#    bdd.configure(reordering=True)

    def NEW(v):
        return v + "'"
    def OLD(v):
        return v

    oldvars = [ OLD(v) for v in allvars ]
    newvars = [ NEW(v) for v in allvars ]

    bddvars = oldvars + newvars

    bdd.declare(*bddvars)

    # Variable orderings

    goodorder = list()
    for v in allvars:
        goodorder.extend([OLD(v),NEW(v)])
    badorder = list(allvars)
    for v in allvars:
        badorder.extend([NEW(v)])

    def list_to_dict(c):
        return {var: level for level, var in enumerate(c)}
#    _bdd.reorder(bdd,list_to_dict(badorder))
    _bdd.reorder(bdd,list_to_dict(goodorder))

    # Mappings x => x' and x' => x
    
    old2new = {}
    new2old = {}

    for v in allvars:
        old2new[OLD(v)] = NEW(v)
        new2old[NEW(v)] = OLD(v)

    # Translate all transitions to logic and further to BDDs

    def trans2logic(t):
        n,c,e = t
        return (n,transition2logic(t,allvars)) # Keep name

    transfmas = [ trans2logic(t) for t in transitions ]

    def atom4bdd(a):
        v,t = a
        if t == 0:
            return OLD(v)
        else:
            return NEW(v)

    transbdds = [ (n,f.varmap(atom4bdd).makeBDD(bdd)) for n,f in transfmas ]

    # Build BDD for the relation for all transitions

    print("Constructing BDD for the transition relation")

    transrelation = model2logic(transitions,allvars)
    transbdd = transrelation.varmap(atom4bdd).makeBDD(bdd)

    print("Transition relation completed: size " + str(len(transbdd)))
    
    # Build BDD for the target states formula

    transdata = (transbdd,newvars,oldvars,old2new,new2old)
    CTLbdd = target.modelCheck(bdd,transdata)

    # Build BDD from the initial state formula

    initialbdd = source.makeBDD(bdd)

    # Check if CTL formula satisfied by the initial state

    if bdd.apply('and',initialbdd,CTLbdd) == bdd.false:
        print("No initial state satisfies " + str(target))
    else:
        print("At least one initial state satisfies " + str(target))

# Main procedure for reading the input file and calling the model-checker
def main():
    if len(sys.argv) != 2:
        print("Must give exactly one argument [file]")
        exit(1)
    args = sys.argv
    filename = args[1]
    print("Input file: " + filename)
    source,target,transitions = parseinputfile(filename)
    gsource,gtarget,gtransitions,allboolvars,allnumvars = groundmodel(source,target,transitions)
    if len(allnumvars) > 0:
        print("Cannot solve numeric problems with BDDs")
        exit(1)
    ctlmodelcheck(gsource,gtarget,gtransitions,allboolvars)

main()
