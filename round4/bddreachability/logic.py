#!/usr/bin/python3

import itertools

# Helper function for iterating bdd.apply over a list

def applyforlist(bddop,formulas,bdd,foremptylist):
  if len(formulas) == 0:
    return foremptylist
  first,rest = formulas[0], formulas[1:]
  headbdd = first.makeBDD(bdd)
  if len(rest) == 0:
    return headbdd
  tailbdd = applyforlist(bddop,rest,bdd,foremptylist)
  return bdd.apply(bddop,headbdd,tailbdd)

# Representation of propositional formulas in Python.
#
# The basic connectives are NEG, CONJ and DISJ.
# IMPL and EQVI are reduced to these through the obvious reductions.
# We have a separate class for formulas with different outermost
# connectives, as well as for atomic formulas (AT).
#
# The methods supported are:
#   vars(self)         Variables occurring in the formula
#   atommap(self,M)    Formula with every AT(a) replaced by M(a)
#   makeBDD(self,bdd)  Construct an OBDD from the formula
#

# AT class represent atomic propositions.
# __repr__ handles two kinds of atomic propositions:
#   string          Represented as is
#   (string,number) Represented in the form string@number

class AT:
  def __init__(self,name):
    self.name = name
  def __repr__(self):
    if isinstance(self.name,str): # Just plain string name
      return self.name
    s,t = self.name # Otherwise pair (string name, integer time)
    return s + "@" + str(t)
  def vars(self):
    return {self.name}
  def atommap(self,M):
    return M(self.name)
  def makeBDD(self,bdd):
    return bdd.var(self.name)

# Both CONJ and DISJ will inherit __init__ and vars from NaryFormula
# NaryFormula means formulas with multiple subformulas.
# Conjunction (CONJ) and disjunction (DISJ) are traditionally defined
# as binary connectives, that is, with two subformulas.
# Because of associativity, ie. A & (B & C) and (A & B) & C are equivalent,
# it is often more convenient to write A & B & C.

class NaryFormula: # N-ary formulas with multiple subformulas
  def __init__(self,subformulas):
    self.subformulas = subformulas
  def vars(self):
    vs = [ f.vars() for f in self.subformulas ]
    return set.union(*vs)

class CONJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two conjuncts
      return "(" + str(self.subformulas[0]) + " and " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 conjuncts
      return "(and " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def atommap(self,M):
    return CONJ([f.atommap(M) for f in self.subformulas])
  def makeBDD(self,bdd):
    return applyforlist('and',self.subformulas,bdd,bdd.true)

class DISJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two disjuncts
      return "(" + str(self.subformulas[0]) + " or " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 disjuncts
      return "(or " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def atommap(self,M):
    return DISJ([f.atommap(M) for f in self.subformulas])
  def makeBDD(self,bdd):
    return applyforlist('or',self.subformulas,bdd,bdd.false)

class NEG:
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(not " + str(self.subformula) + ")"
  def vars(self):
    return self.subformula.vars()
  def atommap(self,M):
    return NEG(self.subformula.atommap(M))
  def makeBDD(self,bdd):
    return ~ self.subformula.makeBDD(bdd)

class TRUE:
  def __init__(self):
    self.name = "TRUE"
  def __repr__(self):
    return "TRUE"
  def vars(self):
    return set()
  def atommap(self,M):
    return self
  def makeBDD(self,bdd):
    return bdd.true

class FALSE:
  def __init__(self):
    self.name = "FALSE"
  def __repr__(self):
    return "FALSE"
  def vars(self):
    return set()
  def atommap(self,M):
    return self
  def makeBDD(self,bdd):
    return bdd.false

# Implication and equivalence reduced to the primitive connectives

# A -> B is reduced to -A V B

def IMPL(f1,f2):
  return DISJ([NEG(f1),f2])

# A <-> B is reduced to (-A V B) & (-B V A)

def EQVI(f1,f2):
  return CONJ([IMPL(f1,f2),IMPL(f2,f1)])

#
# Arithmetic expressions
#

class NumPLUS:
  def __init__(self,e1,e2):
    self.expr1 = e1
    self.expr2 = e2
  def eval(self,V):
    return self.expr1.eval(V) + self.expr2.eval(V)
  
class NumMINUS:
  def __init__(self,e1,e2):
    self.expr1 = e1
    self.expr2 = e2
  def eval(self,V):
    return self.expr1.eval(V) - self.expr2.eval(V)
  
class NumTIMES:
  def __init__(self,e1,e2):
    self.expr1 = e1
    self.expr2 = e2
  def eval(self,V):
    return self.expr1.eval(V) * self.expr2.eval(V)

class NumINTVAR:
  def __init__(self,n):
    self.name = n
  def eval(self,V):
    return V(self.name)

class NumINTCONST:
  def __init__(self,c):
    self.value = c
  def eval(self,V):
    return self.value
