
from logic import *

# State variable x in the current and the next state, which
# often are written as x and x'. Here we form a pair (x,t),
# where t is either 0 or 1. Hence (x,0) denotes the value
# of x in the old state and (x,1) denotes the value of x
# in the new state.

def VARnow(x):
    return (x,0)
def VARnext(x):
    return (x,1)

# Atom with 0 for the value in the current time point
def ATOMnow(x):
    return AT(VARnow(x))

# Atom with 1 for the value in the next time point
def ATOMnext(x):
    return AT(VARnext(x))

# Extract the state variable x from an effect x := b
def varInEffect(e):
    x,b = e
    return x

# Formula x' or NOT x' for an effect x := 1 or x := 0
# Effect are represented as pairs (x,0) or (x,1).

def effect2formula(e):
    v,w = e
    if w == 0: # state variable becomes FALSE
        return NEG(ATOMnext(v))
    else: # state variable becomes TRUE
        return ATOMnext(v)

# Inertia for unchanging x: x <-> x'

def inertia2formula(x):
    return EQVI(ATOMnow(x),ATOMnext(x))

# Formula for one transition

def transition2logic(transition,allvars):
    actionname,condition,effect = transition

    # Include the time 0 in every atom in the condition
    conditionWithTime = condition.atommap(ATOMnow)

    # Formulas for all of the effects of the transition
    eformulas = [ effect2formula(e) for e in effect ]

    # Variables that are assigned a value by the effects
    changing = { varInEffect(e) for e in effect }

    # Variables that are not changed by the effects
    notchanging = allvars.difference(changing)

    # Formulas for "no change" for every non-changing state variable
    inertia = [ inertia2formula(v) for v in notchanging ]

    # Formula for the transition
    return CONJ([conditionWithTime] + eformulas + inertia)

# Translate all transitions to logic

def model2logic(source,target,actions,allvars):
    transitions = [ transition2logic(a,allvars) for a in actions ]
    return DISJ(transitions)
