
#
# Grounding of parametric transitions
#

from logic import *

# Given a transition system, and "ground" it, that is,
# map each parameterized transition rules to a set of
# unparameterized ("ground") transitions rules.

# Consider an transition/action with parameters x : {a,b}, y : {c,d}.
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

# Instantiate a term for given variable bindings
# Terms are either
#   variables referred to in the bindings
#   alphanumeric constants
#   numeric expressions that refer to variables in the bindings

def instantiateterm(t,bindings):
    for e in bindings:
        k,v = e
        if k==t:
            return str(v) # It is a bound variable
    if isinstance(t,str): # It is a constant symbol
        return t
    # Otherwise it is a numeric expression
    def V(x):
        for e in bindings:
            k,v = e
            if k==x:
                return v # It is a bound variable
        return x # It is a constant symbol
    return str(t.eval(V)) # Evaluate the expression
    
# Instantiate an atom for given variable bindings
# Atoms are pairs (pred,termlist)

def instantiateatom(a,bindings):
    pred,termlist = a
    if len(termlist) == 0:
        return pred
    itermlist = map( (lambda t : instantiateterm(t,bindings)) ,termlist)
    return pred + "_" + '_'.join(itermlist)

# Instantiate a formula for given variable bindings

def instantiatefma(f,bindings):
    M = (lambda a : AT(instantiateatom(a,bindings)))
    return f.atommap(M)

# Instantiate an effect for given variable bindings
# Effects are pairs (atom,b) where b=0 or b=1.

def instantiateeff(e,bindings):
    a,tval = e
    return (instantiateatom(a,bindings),tval)

def instantiateeffs(ee,bindings):
    return [ instantiateeff(e,bindings) for e in ee ]

# Make a name for an action with the parameter bindings

def makeName(actionname,bindings):
    if len(bindings) == 0:
        return actionname
    return actionname + "_" + '_'.join([ str(b[1]) for b in bindings ])

# Go through all variable bindings

def doallassignments(actionname,params,precon,effect,bindings):
    if params == []:
        return [(makeName(actionname,bindings),instantiatefma(precon,bindings),instantiateeffs(effect,bindings))]
    param,*params2 = params
    var,values = param
    result = [ doallassignments(actionname,params2,precon,effect,bindings + [(var,val)]) for val in values ]
    return sum(result,[])

# Ground one action

def groundaction(a):
    actionname,params,precon,effect = a
    return doallassignments(actionname,params,precon,effect,list())

# Show effect

def printeff(e):
    a,t = e
    print(a,end='')
    if t == 1:
        print(" = 1",end =' ')
    elif t == 0:
        print(" = 0",end =' ')
    else:
        print("ERROR")

# Top-level procedure for grounding.

# Extract the state variable x from an effect x := b
def varInEffect(e):
    x,b = e
    return x

# State variables occurring in an action (its condition and the effects)
def actionVars(g):
    n,c,e = g
    return c.vars().union({ varInEffect(a) for a in e })

# Ground a transition system description, with parameterized transition
# rules mapped to ground/unparameterized rules.

def groundmodel(source,target,actions):
    groundtarget = instantiatefma(target,list())
    groundactions = [ g for a in actions for g in groundaction(a) ]
    allvars0 = groundtarget.vars().union({ v for g in groundactions for v in actionVars(g)})
    if isinstance(source,list):
        groundsource = [ instantiateatom(x,list()) for x in source ]
        allvars = allvars0.union({ x for x in groundsource})
    else:
        groundsource = instantiatefma(source,list())
        allvars = allvars0.union(groundsource.vars())
    print("ALL STATE VARIABLES: " + ' '.join(sorted(allvars)))
    print("GROUNDED ACTIONS:")
    for a in groundactions:
        n,p,e = a
        print("NAME:" + n)
        print("PREC:",end='')
        print(p)
        print("EFF:",end='')
        for ae in e:
            printeff(ae)
        print("\n")
    print("GROUNDED TARGET:")
    print(groundtarget)
    return (groundsource,groundtarget,groundactions,allvars)
