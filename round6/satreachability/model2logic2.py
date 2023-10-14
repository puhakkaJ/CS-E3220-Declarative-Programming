
from logic2 import *
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

def makeNumChange(x,effect):
    changes = effect.nepc(x)
    noChange = CONJ([ NEG(c) for c,e in changes ])
    return CONJ([IMPL(noChange,NumEQ(NumINTVAR( (x,0) ),NumINTVAR( (x,1) )))]
                + [IMPL(c,NumEQ(NumINTVAR( (x,1) ),e.varmap( (lambda x : (x,0)) ))) for c,e in changes])

# Formula for change of a numeric state variable

def makeBoolChange(x,effect):
    makesTrue = effect.epc(x,True)
    makesFalse = effect.epc(x,False)
    return EQVI(ATOMnext(x),
                DISJ([makesTrue.varmap( VARnow ),
                      CONJ([ATOMnow(x),NEG(makesFalse.varmap ( VARnow ))])]))

# Formula for one transition

def transition2logic(transition,allboolvars,allnumvars):
    actionname,condition,effect = transition
    
    # Change for Boolean formulas

    boolaxioms = [ makeBoolChange(x,effect) for x in allboolvars ]

    numaxioms = [ makeNumChange(x,effect) for x in allnumvars ]
    
    return CONJ([condition.varmap(VARnow)] + boolaxioms + numaxioms)

# Translate all transitions to logic

def model2logic(actions,allboolvars,allnumvars):
    transitions = [ transition2logic(a,allboolvars,allnumvars) for a in actions ]
    return DISJ(transitions)
