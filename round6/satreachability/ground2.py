
#
# Grounding of parametric transition definitions
#

from logic2 import *
from effects import *

# Given a transition system, ground it, and translate into
# a set of formulas in the propositional logic.

# Consider an action with parameters x : {a,b}, y : {c,d}.
# We need to create all possible value combinations for x and y,
# and these are represented by the four variable bindings
# [ (x,a), (y,c) ]
# [ (x,a), (y,d) ]
# [ (x,b), (y,c) ]
# [ (x,b), (y,d) ]
# The function doallassignments takes the first parameter
# binds it in all possible ways (e.g. x is bound to 'a' and 'b'),
# and recursively calls itself for each of these cases, until
# all variables are bound. The bottom of the recursion is
# when there are no parameters left to bind, and the 'bindings'
# variable includes every parameter with one value.

# Instantiate a term for given variable bindings, and evaluate
# all numeric expressions.
# Terms are either
#   variables referred to in the bindings
#   alphanumeric constants
#   numeric expressions that refer to variables in the bindings

def instTermEval(t,bindings):
    for e in bindings:
        k,v = e
        if k==t:
            return str(v) # It is a bound variable
    if isinstance(t,str): # If a string is not bound, it's a constant symbol
        return t
    # Otherwise it is a numeric expression
    def V(x):
        for e in bindings:
            k,v = e
            if k==x:
                return v # It is a bound variable
        return x # It is a constant symbol
    return str(t.eval(V)) # Evaluate the expression
    
# Instantiate a term, but do not evaluate anything (as the term
# may still contain variables with no binding.)

def instTerm(t,bindings):
    if isinstance(t,str): # The term is possibly a var with value
        for e in bindings:
            k,v = e
            if k==t:
                return v
        # Has not value. Return as is.
        return t
    # Otherwise it is a numeric expression
    def V(x):
        for e in bindings:
            k,v = e
            if k==x:
                return v # It is a bound variable
        return x # It is a constant symbol
    return t.varmap(V) # Substitute all bound variables
    
# Instantiate an atom for given variable bindings, and evaluate
# possible numeric expressions in the terms.
# Atoms are pairs (pred,termlist)
# Result is a string

def instAtom(a,bindings):
    pred,termlist = a
#    itermlist = map( (lambda t : instTerm(t,bindings)), termlist)
    itermlist = [ instTerm(t,bindings) for t in termlist ]
    return (pred,itermlist)

# Instantiate an expression, with all possible variable bindings

def allExprInstances(params,expr,bindings):
    # If all parameters have a value, instantiate with these parameter values
    if params == []:
        return [expr.varmap( (lambda a : instAtom(a,bindings)) )]
    # Otherwise go through all values for the first parameter, with recursive calls
    param,*params2 = params
    var,values = param
    result = [ allExprInstances(params2,expr,bindings + [(var,val)]) for val in values ]
    return sum(result,[])

# Instantiate an effect, with all possible variable bindings

def allEffectInstances(params,effect,bindings):
    # If all parameters have a value, instantiate with these parameter values
    if params == []:
        return [ effect.varmap( (lambda a : instAtom(a,bindings)) ) ]
    # Otherwise go through all values for the first parameter, with recursive calls
    param,*params2 = params
    var,values = param
    result = [ allEffectInstances(params2,effect,bindings + [(var,val)]) for val in values ]
    return sum(result,[])

# Instantiate an atom for given variable bindings, and evaluate
# possible numeric expressions in the terms.
# Atoms are pairs (pred,termlist)
# Result is a string

def instAtomEval2Str(a,bindings):
    pred,termlist = a
    if len(termlist) == 0:
        return pred
#    itermlist = map( (lambda t : instTermEval(t,bindings)), termlist)
    itermlist = [ instTermEval(t,bindings) for t in termlist ]
    return pred + "_" + '_'.join(itermlist)

# Make a name for an action with the parameter bindings

def makeName(actionname,bindings):
    if len(bindings) == 0:
        return actionname
    return actionname + "_" + '_'.join([ str(b[1]) for b in bindings ])

# Instantiate an action, with all possible variable bindings, and
# evaluating all expressions in precondition and effects.

def allActionInstances(actionname,params,precon,effect,bindings):
    # If all parameters have a value, instantiate with these parameter values
    if params == []:
        return [(makeName(actionname,bindings),precon.varmap( (lambda a : instAtomEval2Str(a,bindings)) ), effect.varmap( (lambda a : instAtomEval2Str(a,bindings)) ))]
    # Otherwise go through all values for the first parameter, with recursive calls
    param,*params2 = params
    var,values = param
    result = [ allActionInstances(actionname,params2,precon,effect,bindings + [(var,val)]) for val in values ]
    return sum(result,[])

# Grounding of one action, generating all instances

def groundaction(a):
    actionname,params,precon,effect = a
    return allActionInstances(actionname,params,precon,effect,list())

# Top-level procedure for grounding

# Extract Boolean state variables in an action

def actionBoolVars(g):
    n,c,e = g
    return c.vars().union(e.vars())

# Find all numeric variables in an action

def actionNumVars(g):
    n,c,e = g
    return c.numvars().union(e.numvars())

# Instantiate with the empty bindings

def bareinstantiate(a):
    return instAtomEval2Str(a,list())

def groundmodel(source,target,trajectory,actions):
    if target == None:
        groundtarget = TRUE()
    else:
        groundtarget = target.varmap(bareinstantiate)
    groundactions = [ g for a in actions for g in groundaction(a) ]
    allboolvars0 = groundtarget.vars().union({ v for g in groundactions for v in actionBoolVars(g)})
    allnumvars0 = groundtarget.numvars().union({ v for g in groundactions for v in actionNumVars(g)})
    if isinstance(source,list):
        boolinits = [ bareinstantiate((p,tt)) for p,tt in source if isinstance(p,str) ]
        numinits = [ (bareinstantiate(v),c) for v,c in source if not(isinstance(v,str)) ]
        explicitnums = [ x for x,e in numinits ]

        explicitinit = [ AT(x) for x in boolinits ]
        implicitinit = [ NEG(AT(x)) for x in allboolvars0 if not(x in boolinits) ]
        explicitnuminit = [ NumEQ(NumINTVAR(x),NumINTCONST(c)) for x,c in numinits ]
        implicitnuminit = [ NumEQ(NumINTVAR(x),NumINTCONST(0)) for x in allnumvars0 if x not in explicitnums ]
        groundsource = CONJ(explicitinit + implicitinit + implicitnuminit + explicitnuminit)
    elif source != None:
        groundsource = source.varmap(bareinstantiate)
    else:
        groundsource = TRUE()
    if trajectory != None:
        groundtrajectory = trajectory.varmap(bareinstantiate)
    else:
        groundtrajectory = None
    allboolvars = allboolvars0.union(groundsource.vars())
    allnumvars = allnumvars0.union(groundsource.numvars())
    if target == None:
        groundtarget = None
    SHOWRESULT = False
    if SHOWRESULT:
        print("ALL STATE VARIABLES: " + ' '.join(sorted(allboolvars)))
        print("GROUNDED ACTIONS:")
        for a in groundactions:
            n,p,e = a
            print("NAME:" + n)
            print("PREC:",end='')
            print(str(p))
            print("EFF:",end='')
            print(str(e))
            print("\n")
        if not isinstance(target,int):
            print("GROUNDED TARGET:")
            print(groundtarget)
    return (groundsource,groundtarget,groundtrajectory,groundactions,allboolvars,allnumvars)
