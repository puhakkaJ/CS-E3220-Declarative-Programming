
from modallogic import *

# Exceptions for lexer and parser error handling

class ParserSyntaxError(Exception):
    pass

class LexerReadError(Exception):
    pass

#################### Lexer

# all tokens

tokens = (
    'ID',
    'AND','OR','NOT','EQVI','IMPL',
    'PTRUE', 'PFALSE',
    'LPAREN','RPAREN',
    'SEMICOLON', 'COMMA',
    'LBRACE', 'RBRACE',
    'POSS', 'NECE',
    'MODEL', 'END'
    )

# Tokens are the lexical elements as recognized by the lexical analyzer
# The names of all tokens start with t_ .

t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBRACE  = r'\{'
t_RBRACE  = r'\}'
t_SEMICOLON = r';'
t_COMMA = r'\,'

# Ignored characters
t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    
# Comments in the specifications start with # just like in Python

def t_COMMENT(t):
    r'\#.*'
    print(t.value)
    pass
    # No return value. Token discarded

# Process characters that are not handled by the lexer
    
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)
    raise LexerReadError

# IDs and reserved words

# Mapping from reserved words to tokens

keywords = {'and': 'AND',
            'or': 'OR',
            'not': 'NOT',
            'eqvi': 'EQVI',
            'impl': 'IMPL',
            'TRUE' : 'PTRUE',
            'FALSE' : 'PFALSE',
            'NECE' : 'NECE',
            'POSS' : 'POSS',
            'model' : 'MODEL',
            'end' : 'END'
            }

# Alphanumeric tokens

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z0-9_]*'
    if t.value in keywords:
        t.type = keywords[t.value]
    return t
    
# Build the lexer
import ply.lex as lex
lexer = lex.lex()

####### Data to be filled in by the parser/lexer

####### Parser

# How strongly do the different operators bind, and whether the operator
# is left or right associative. This is important when there are no
# parentheses to disambiguate.
# For example, 1+2+3 means (1+2)+3, and 1+2*3 means 1+(2*3).
# Weaker operators are given first, stronger ones later.

precedence = (
    ('right','EQVI'),
    ('right','IMPL'),
    ('left','AND','OR'),
    ('left','NOT'), ('left','POSS'), ('left','NECE')
    )

# Parsing rules

# This is a context-free grammar (ply probably implement LALR grammars).
# In a rule  'nonterminal | el1 el2 el3 ... elN'
# the values associated with the syntactic elements el1,el2,...,elN
# (which are either terminals (as recognized by the lexical analyzer)
#  or terminals) can be accessed as t[1],t[2],...,t[N], and
# the value to be associated with the 'nonterminal' is assigned to t[0].

# Global variables where the Kripke model and the formulas will be stored

kripkemodel = None
formulas = []

# Top-level definitions

def p_spec(t):
    '''spec : kripkemodel formulas'''
    global kripkemodel
    global formulas
    kripkemodel = t[1]
    formulas = t[2]

def p_formulas_1(t):
    '''formulas : formula SEMICOLON'''
    t[0] = [t[1]]

def p_formulas_N(t):
    '''formulas : formulas formula SEMICOLON'''
    t[0] = t[1] + [t[2]]

# Definition of a Kripke model as a list of entries of the form
#
#   world LBRACE a1, a2, ..., an RBRACE w1, w2, ..., wm SEMICOLON
#
# where 'world' is an alphanumeric name of a world
#       a1, ..., an are atoms (with alphanumeric names) true in 'world'
#       w2, ..., wm are 0 or more worlds accessible from 'world'

def p_kripkemodel(t):
    '''kripkemodel : MODEL worldlist END MODEL'''
    TRUE = dict() # Valuations for every world
    NEIGH = dict() # Neighbors for every world
    for w,T,N in t[2]:
        TRUE[w] = T
        NEIGH[w] = N
    t[0] = KripkeModel([ w for w,T,N in t[2]],TRUE,NEIGH)

def p_worldlist_1(t):
    '''worldlist : world'''
    t[0] = [t[1]]

def p_worldlist_N(t):
    '''worldlist : worldlist world'''
    t[0] = t[1] + [t[2]]

def p_world(t):
    '''world : ID LBRACE stringlist RBRACE stringlist SEMICOLON'''
    t[0] = (t[1],t[3],t[5])

def p_stringlist_0(t):
    '''stringlist :'''
    t[0] = []

def p_stringlist_N(t):
    '''stringlist : stringlist1'''
    t[0] = t[1]

def p_stringlist_1(t):
    '''stringlist1 : ID'''
    t[0] = [t[1]]

def p_stringlist_1N(t):
    '''stringlist1 : stringlist1 COMMA ID'''
    t[0] = t[1] + [t[3]]

# Propositional modal formulas

# Binary connectives

def p_formula_binop(t):
    '''formula : formula AND formula
                | formula OR formula
                | formula IMPL formula
                | formula EQVI formula'''
    if t[2] == 'and'   : t[0] = CONJ([t[1],t[3]])
    elif t[2] == 'or'  : t[0] = DISJ([t[1],t[3]])
    elif t[2] == 'impl': t[0] = IMPL(t[1],t[3])
    elif t[2] == 'eqvi': t[0] = EQVI(t[1],t[3])

# The unary connective for negation

def p_formula_unop_neg(t):
    'formula : NOT formula'
    t[0] = NEG(t[2])

# The unary connective for possible (diamond)

def p_formula_unop_pos(t):
    'formula : POSS formula'
    t[0] = POSS(t[2])

# The unary connective for necessary (box)

def p_formula_unop_nec(t):
    'formula : NECE formula'
    t[0] = NECE(t[2])

# Boolean constants TRUE and FALSE

def p_formula_true(t):
    'formula : PTRUE'
    t[0] = TRUE()

def p_formula_false(t):
    'formula : PFALSE'
    t[0] = FALSE()

# Atomic propositions

def p_formula_atom(t):
    'formula : ID'
    t[0] = AT(t[1])

# Parentheses around Boolean formulas

def p_formula_parentheses(t):
    '''formula : LPAREN formula RPAREN'''
    t[0] = t[2]

# Error rule

def p_error(t):
    print("Syntax error at '%s' on line %i" % (t.value,t.lexer.lineno))
    raise ParserSyntaxError

import ply.yacc as yacc
parser = yacc.yacc()

def parseinputfile(filename):
    global kripkemodel
    global formulas
    with open(filename, 'r') as f:
        allinput = f.read()
        parser.parse(allinput)
    return kripkemodel,formulas
