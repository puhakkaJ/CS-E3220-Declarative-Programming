
#!/usr/bin/python3

import itertools

# A Kripke model
#   self.worlds : list of names of all worlds (strings)
#   self.valuation : a dictionary indexed with world names, containing
#                    lists of atoms that are true in a given world.
#   self.neighbordict : a dictionary indexed with world names, containing
#                       lists of world names accessible from a given world.

class KripkeModel:
    def __init__(self,worlds,valuation,neighbors):
        self.worlds = worlds
        self.valuation = valuation
        self.neighbordict = neighbors

    # Return True if atom 'atomname' is true in 'world', and False otherwise.

    def atomval(self,world,atomname):
        return atomname in self.valuation[world]

    # Return neighbors, that is, accessible worlds.

    def neighbors(self,world):
        return self.neighbordict[world]

# Representation of propositional modal formulas
#
# The basic connectives are NEG, CONJ and DISJ.
# IMPL and EQVI are reduced to these through the obvious reductions.
# Modal operators NECE (for 'necessarily') and POSS (for 'possibly').
#
# The methods are:
#   eval(self,KM,w)    Truth-value in world 'w' of a Kripke model KM
#

# AT class represents atomic propositions, with a string name.

class AT:
  def __init__(self,name):
    self.name = name
  def __repr__(self):
      return self.name
  def eval(self,KM,w):
    return KM.atomval(w,self.name)

# Both CONJ and DISJ will inherit __init__ and vars from NaryFormula
# NaryFormula means formulas with multiple subformulas.
# Conjunction (CONJ) and disjunction (DISJ) are traditionally defined
# as binary connectives, that is, with two subformulas.
# Because of associativity, ie. A & (B & C) and (A & B) & C are equivalent,
# it is often more convenient to write A & B & C.

class NaryFormula: # N-ary formulas with multiple subformulas
  def __init__(self,subformulas):
    self.subformulas = subformulas

class CONJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two conjuncts
      return "(" + str(self.subformulas[0]) + " and " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 conjuncts
      return "(and " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def eval(self,KM,w):
    for f in self.subformulas:
      if not f.eval(KM,w):
        return False
    return True

class DISJ(NaryFormula):
  def __repr__(self):
    if len(self.subformulas) == 2: # Infix notation if two disjuncts
      return "(" + str(self.subformulas[0]) + " or " + str(self.subformulas[1]) + ")"
    else: # Prefix notation if 1 or more than 2 disjuncts
      return "(or " + (' '.join([ str(x) for x in self.subformulas])) + ")"
  def eval(self,KM,w):
### YOUR CODE HERE
### YOUR CODE HERE
### YOUR CODE HERE
### YOUR CODE HERE

class NEG:
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(not " + str(self.subformula) + ")"
  def eval(self,KM,w):
### YOUR CODE HERE

class NECE:
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(NECE " + str(self.subformula) + ")"
  def eval(self,KM,w):
### YOUR CODE HERE

class POSS:
  def __init__(self,subformula):
    self.subformula = subformula
  def __repr__(self):
    return "(POSS " + str(self.subformula) + ")"
  def eval(self,KM,w):
### YOUR CODE HERE

class TRUE:
  def __init__(self):
    self.name = "TRUE"
  def __repr__(self):
    return "TRUE"
  def eval(self,KM,w):
    return True

class FALSE:
  def __init__(self):
    self.name = "FALSE"
  def __repr__(self):
    return "FALSE"
  def eval(self,KM,w):
    return False

# Implication and equivalence reduced to the primitive connectives

# A -> B is reduced to -A V B

def IMPL(f1,f2):
  return DISJ([NEG(f1),f2])

# A <-> B is reduced to (-A V B) & (-B V A)

def EQVI(f1,f2):
  return CONJ([IMPL(f1,f2),IMPL(f2,f1)])
