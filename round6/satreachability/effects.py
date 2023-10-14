
from logic2 import *

# Methods for effect classes
#
# vars : all Boolean variables occurring in the effect
# numvars : all numeric variables occurring in the effect
# varmap : replace every variable x by M(x)
# epc : condition under which given Boolean variable becomes true or false
# nepc : conditions,expressions under which given numeric variable is assigned
# changes : variable,newvalue changes caused by effect in a given state

# Atomic effects

class MAKETRUE:
  def __init__(self,statevar):
    self.statevar = statevar
  def __repr__(self):
    return self.statevar + " := TRUE"
  def vars(self):
    return {self.statevar}
  def numvars(self):
    return set()
  def varmap(self,M):
    return MAKETRUE(M(self.statevar))
  def epc(self,x,ispos):
    if ispos and self.statevar == x:
      return TRUE()
    else:
      return FALSE()
  def nepc(self,x):
    return []
  def changes (self,s):
    return [(self.statevar,True)]

class MAKEFALSE:
  def __init__(self,statevar):
    self.statevar = statevar
  def __repr__(self):
    return self.statevar + " := FALSE"
  def vars(self):
    return {self.statevar}
  def numvars(self):
    return set()
  def varmap(self,M):
    return MAKEFALSE(M(self.statevar))
  def epc(self,x,ispos):
    if not ispos and self.statevar == x:
      return TRUE()
    else:
      return FALSE()
  def nepc(self,x):
    return []
  def changes (self,s):
    return [(self.statevar,False)]

class ASSIGN:
  def __init__(self,statevar,expr):
    self.statevar = statevar
    self.expr = expr
  def __repr__(self):
    return self.statevar + " := " + str(self.expr)
  def vars(self):
    return set()
  def numvars(self):
    return {self.statevar}.union(self.expr.numvars())
  def varmap(self,M):
    return ASSIGN(M(self.statevar),self.expr.varmap(M))
  def epc(self,x,ispos):
    return FALSE()
  def nepc(self,x):
    if x==self.statevar:
      return [(TRUE(),self.expr)]
    else:
      return []
  def changes (self,s):
    return [(self.statevar,self.expr.eval(s))]

# Conditional effects

class IFTHEN:
  def __init__(self,cond,effect):
    self.condition = cond
    self.effect = effect
  def __repr__(self):
    return " IF " + str(cond) + str(self.effect)
  def vars(self):
    return self.condition.vars().union(self.effect.vars())
  def numvars(self):
    return self.condition.numvars().union(self.effect.numvars())
  def varmap(self,M):
    return IFTHEN(self.condition.varmap(M),self.effect.varmap(M))
  def epc(self,x,ispos):
    return CONJ([self.condition, self.effect.epc(x,ispos)])
  def nepc(self,x):
    return [ (CONJ([self.condition,c]),e) for c,e in self.effect.nepc(x) ]
  def changes(self,s):
    if self.condition.eval(s):
      return self.effect.changes(s)
    return []

# Multiple effects in parallel

class EFFLIST:
  def __init__(self,effects):
    self.effects = effects
  def __repr__(self):
    return " { " + '; '.join([ str(e) for e in self.effects ]) + " } "
  def vars(self):
    vs = [ f.vars() for f in self.effects ]
    return set.union(*vs)
  def numvars(self):
    vs = [ f.numvars() for f in self.effects ]
    return set.union(*vs)
  def varmap(self,M):
    return EFFLIST([ e.varmap(M) for e in self.effects ])
  def epc(self,x,ispos):
    return DISJ([ e.epc(x,ispos) for e in self.effects ])
  def nepc(self,x):
    ns = [ e.nepc(x) for e in self.effects]
    return set().union(*ns)
  def changes(self,s):
    return [ c for e in self.effects for c in e.changes(s)  ]
