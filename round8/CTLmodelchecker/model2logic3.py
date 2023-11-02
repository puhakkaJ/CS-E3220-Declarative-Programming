
from CTLlogic import *
from effects import *

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

# Formula for change of a Boolean state variable

def makeBoolChange(x,effect):
    makesTrue = effect.epc(x,True)
    makesFalse = effect.epc(x,False)
    return EQVI(ATOMnext(x),
                DISJ([makesTrue.varmap( VARnow ),
                      CONJ([ATOMnow(x),NEG(makesFalse.varmap ( VARnow ))])]))

# Formula for one transition

def transition2logic(transition,allboolvars):
    actionname,condition,effect = transition
    
    # Change for Boolean formulas

    boolaxioms = [ makeBoolChange(x,effect) for x in allboolvars ]

    return CONJ([condition.varmap(VARnow)] + boolaxioms)

# Translate all transitions to logic

def model2logic(actions,allboolvars):
    transitions = [ transition2logic(a,allboolvars) for a in actions ]
    return DISJ(transitions)
