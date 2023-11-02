#!/usr/bin/python3

import itertools

# Helper function for iterating bdd.apply over a list of BDDs

def applyforlist(bddop,bdds,bdd,foremptylist):
  if len(bdds) == 0:
    return foremptylist
  first,rest = bdds[0], bdds[1:]
  if len(rest) == 0:
    return first
  tailbdd = applyforlist(bddop,rest,bdd,foremptylist)
  return bdd.apply(bddop,first,tailbdd)

# Representation of propositional formulas in Python.
#
# The basic connectives are NEG, CONJ and DISJ.
# IMPL and EQVI are reduced to these through the obvious reductions.
# We have a separate class for formulas with different outermost
# connectives, as well as for atomic formulas (AT).
#
# The methods supported are:
#   vars(self)         Boolean variables occurring in the formula
#   numvars(self)      Numeric variables occurring in the formula
#   varmap(self,M)     Formula with every variable x replaced by M(x)
#   atommap(self,M)    Formula with every AT(a) replaced by M(a)
#   makeBDD(self,bdd)  Construct an OBDD from the formula
#   modelCheck(self,bdd,transdate)  
#                      Construct BDD for states that satisfy CTL formula
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
  def numvars(self):
    return set()
  def varmap(self,M):
    return AT(M(self.name))
  def makeBDD(self,bdd):
    return bdd.var(self.name)
  def eval(self,V):
    return V(self.name)
  def modelCheck(self,bdd,transdata):
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
  def numvars(self):
    vs = [ f.numvars() for f in self.subformulas ]
    return set.union(*vs)

class CONJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two conjuncts
      return "(" + str(self.subformulas[0]) + " and " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 conjuncts
      return "(and " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def varmap(self,M):
    return CONJ([f.varmap(M) for f in self.subformulas])
  def makeBDD(self,bdd):
    return applyforlist('and',[ f.makeBDD(bdd) for f in self.subformulas ],bdd,bdd.true)
  def eval(self,V):
    for f in self.subformulas:
      if not f.eval(V):
        return False
    return True
  def modelCheck(self,bdd,transdata):
    return applyforlist('and',[ f.modelCheck(bdd,transdata) for f in self.subformulas ],bdd,bdd.true)

class DISJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two disjuncts
      return "(" + str(self.subformulas[0]) + " or " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 disjuncts
      return "(or " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def varmap(self,M):
    return DISJ([f.varmap(M) for f in self.subformulas])
  def makeBDD(self,bdd):
    return applyforlist('or',[ f.makeBDD(bdd) for f in self.subformulas ],bdd,bdd.false)
  def eval(self,V):
    for f in self.subformulas:
      if f.eval(V):
        return True
    return False
  def modelCheck(self,bdd,transdata):
    return applyforlist('or',[ f.modelCheck(bdd,transdata) for f in self.subformulas ],bdd,bdd.false)

class NEG:
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(not " + str(self.subformula) + ")"
  def vars(self):
    return self.subformula.vars()
  def numvars(self):
    return self.subformula.numvars()
  def varmap(self,M):
    return NEG(self.subformula.varmap(M))
  def makeBDD(self,bdd):
    return ~ self.subformula.makeBDD(bdd)
  def eval(self,V):
    return not(self.subformula.eval(V))
  def modelCheck(self,bdd,transdata):
    return ~ self.subformula.modelCheck(bdd,transdata)

class TRUE:
  def __init__(self):
    self.name = "TRUE"
  def __repr__(self):
    return "TRUE"
  def vars(self):
    return set()
  def numvars(self):
    return set()
  def varmap(self,M):
    return self
  def makeBDD(self,bdd):
    return bdd.true
  def eval(self,V):
    return True
  def modelCheck(self,bdd,transdata):
    return bdd.true

class FALSE:
  def __init__(self):
    self.name = "FALSE"
  def __repr__(self):
    return "FALSE"
  def vars(self):
    return set()
  def numvars(self):
    return set()
  def varmap(self,M):
    return self
  def makeBDD(self,bdd):
    return bdd.false
  def eval(self,V):
    return False
  def modelCheck(self,bdd,transdata):
    return bdd.false

# Implication and equivalence reduced to the primitive connectives

# A -> B is reduced to -A V B

def IMPL(f1,f2):
  return DISJ([NEG(f1),f2])

# A <-> B is reduced to (-A V B) & (-B V A)

def EQVI(f1,f2):
  return CONJ([IMPL(f1,f2),IMPL(f2,f1)])

# Numeric equalities and inequalities

class NumREL:
  def __init__(self,e1,e2):
    self.e1 = e1
    self.e2 = e2
  def vars(self):
    return set()
  def numvars(self):
    return self.e1.numvars().union(self.e2.numvars())

class NumEQ(NumREL):
  def __repr__(self):
    return "[" + str(self.e1) + " = " + str(self.e2) + "]"
  def varmap(self,M):
    return NumEQ(self.e1.varmap(M),self.e2.varmap(M))
  def eval(self,V):
    return self.e1.eval(V) == self.e2.eval(V)
  
class NumLEQ(NumREL):
  def __repr__(self):
    return "[" + str(self.e1) + " <= " + str(self.e2) + "]"
  def varmap(self,M):
    return NumLEQ(self.e1.varmap(M),self.e2.varmap(M))
  def eval(self,V):
    return self.e1.eval(V) <= self.e2.eval(V)
  
class NumLT(NumREL):
  def __repr__(self):
    return "[" + str(self.e1) + " < " + str(self.e2) + "]"
  def varmap(self,M):
    return NumLT(self.e1.varmap(M),self.e2.varmap(M))
  def eval(self,V):
    return self.e1.eval(V) < self.e2.eval(V)

class NumOP:
  def __init__(self,e1,e2):
    self.e1 = e1
    self.e2 = e2
  def vars(self):
    return set()

  #
# Arithmetic expressions
#

class NumPLUS:
  def __init__(self,e1,e2):
    self.e1 = e1
    self.e2 = e2
  def __repr__(self):
    return "(" + str(self.e1) + " + " + str(self.e2) + ")"
  def eval(self,V):
    return self.e1.eval(V) + self.e2.eval(V)
  def varmap(self,M):
    return NumPLUS(self.e1.varmap(M),self.e2.varmap(M))
  def numvars(self):
    return self.e1.numvars().union(self.e2.numvars())
  
class NumMINUS:
  def __init__(self,e1,e2):
    self.e1 = e1
    self.e2 = e2
  def __repr__(self):
    return "(" + str(self.e1) + " - " + str(self.e2) + ")"
  def eval(self,V):
    return self.e1.eval(V) - self.e2.eval(V)
  def varmap(self,M):
    return NumMINUS(self.e1.varmap(M),self.e2.varmap(M))
  def numvars(self):
    return self.e1.numvars().union(self.e2.numvars())
  
class NumTIMES:
  def __init__(self,e1,e2):
    self.e1 = e1
    self.e2 = e2
  def __repr__(self):
    return "(" + str(self.e1) + " * " + str(self.e2) + ")"
  def eval(self,V):
    return self.e1.eval(V) * self.e2.eval(V)
  def varmap(self,M):
    return NumTIMES(self.e1.varmap(M),self.e2.varmap(M))
  def numvars(self):
    return self.e1.numvars().union(self.e2.numvars())

class NumINTVAR:
  def __init__(self,n):
    self.name = n
  def eval(self,V):
    return V(self.name)
  def __repr__(self):
    if isinstance(self.name,str): # Just plain string name
      return self.name
    s,t = self.name # Otherwise string name with integer tag
    return s + "@" + str(t)
  def numvars(self):
    return {self.name}
  def varmap(self,M):
    return NumINTVAR(M(self.name))

class NumINTCONST:
  def __init__(self,c):
    self.value = c
  def eval(self,V):
    return self.value
  def __repr__(self):
    return str(self.value)
  def numvars(self):
    return set()
  def varmap(self,M):
    return self
  def numvars(self):
    return set()
  
# GT and GEQ reduced to LT and LEQ

def NumGT(e1,e2):
  return NumLT(e2,e1)
def NumGEQ(e1,e2):
  return NumLEQ(e2,e1)

# Helper functions for BDD operations
#
# In these functions, as in many functions elsewhere in this file
# 'bdd' is the OBDD containing all of the Boolean functions of
# interest as subgraphs. This same 'bdd' is passed to all
# functions that manipulate bdds.
# Specific Boolean functions (or formulas) represented as subgraphs
# are given as additional parameters, like 'b1', 'b2' and 'b' in
# the following helper functions.

  # Conjunction

def BDDAND(bdd,b1,b2):
  return bdd.apply('and',b1,b2)

  # Disjunction

def BDDOR(bdd,b1,b2):
  return bdd.apply('or',b1,b2)

  # Renaming

def BDDRENAME(bdd,renaming,b):
  return bdd.let(renaming,b)

  # Existential abstraction

def BDDEXIST(bdd,bddvars,b):
  return bdd.exist(bddvars,b)

# CTL operators NEXT, ALWAYS, UNTIL

class CTLopEX():
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(EX " + str(self.subformula) + ")"
  def vars(self):
    return self.subformula.vars()
  def numvars(self):
    return self.subformula.numvars()
  def varmap(self,M):
    return CTLopEX(self.subformula.varmap(M))
  def modelCheck(self,bdd,transdata):
    # 'transdata' is a 4-tuple containing the following components:
    #    transbdd : The transition relation BDD
    #    newvars : The primed x' variables for all state variables x
    #    oldvars : The unprimed x variables for all state variables x
    #    old2new : Renaming from all unprimed x to primed x'
    #    new2old : Renaming from all primed x' to unprimed x

    transbdd,newvars,oldvars,old2new,new2old = transdata

    # Now we construct a BDD that represents those states in which
    # 'EX f' is true.
    # This is by the OBDD operations for conjunction, renaming, and
    # existential abstraction.
    #
    # 1. Construct a BDD that represents those states in which
    #    'f' is true. This is by recursively calling 'modelCheck' for 'f'.
    # 2. Rename all variables in the resulting OBDD from x to x'.
    # 3. Then conjoin this with the transition relation OBDD 'transbdd'.
    # 4. Existentially abstract away the primed x' variables.
    # This can all be one line of code.
### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###

class CTLopEG():
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(EG " + str(self.subformula) + ")"
  def vars(self):
    return self.subformula.vars()
  def numvars(self):
    return self.subformula.numvars()
  def varmap(self,M):
    return CTLopEG(self.subformula.varmap(M))
  def modelCheck(self,bdd,transdata):
    transbdd,newvars,oldvars,old2new,new2old = transdata
    phibdd = self.subformula.modelCheck(bdd,transdata)
    S = {}
    S[0] = phibdd
    i = 0
    while True:
      S[i+1] = BDDAND(bdd,phibdd,BDDEXIST(bdd,newvars,BDDAND(bdd,transbdd,BDDRENAME(bdd,old2new,S[i]))))
      print("Computation of EG: BDD of size " + str(len(S[i+1])))
      i = i + 1
      if S[i] == S[i-1]:
        print("EG fixpoint at iteration " + str(i) + " for " + str(self))
        break
    return S[i]

class CTLopEU():
  def __init__(self,subformula1,subformula2):
    self.subformula1 = subformula1
    self.subformula2 = subformula2
  def __repr__(self):
    return "(E [ " + str(self.subformula1) + " U " + str(self.subformula2) + " ]"
  def vars(self):
    return self.subformula1.vars().union(self.subformula2.vars())
  def numvars(self):
    return self.subformula1.numvars().union(self.subformula2.numvars())
  def varmap(self,M):
    return CTLopEU(self.subformula1.varmap(M),self.subformula2.varmap(M))
  def modelCheck(self,bdd,transdata):
    transbdd,newvars,oldvars,old2new,new2old = transdata

    # Model-checking the E UNTIL operator is a fix-point computation similar to
    # the model-checking of E G.

### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###
### YOUR # CODE # HERE ###



# Operators defined in terms of the primitive ones EX, EU, EG

def CTLopEF(phi):
  return CTLopEU(TRUE,phi)

def CTLopAG(phi):
  return NEG(CTLopEU(TRUE,NEG(phi)))

def CTLopAF(phi):
  return NEG(CTLopEG(NEG(phi)))

def CTLopAX(phi):
  return NEG(CTLopEX(NEG(phi)))

def CTLopAU(phi,psi):
  return CONJ([NEG(CTLopEU(NEG(phi),CONJ([NEG(phi),NEG(psi)]))),
               NEG(CTLopEG(NEG(psi)))])
