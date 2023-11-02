
from CTLlogic import *
from effects import *
from ground3 import allEffectInstances, allExprInstances

# Exceptions for lexer and parser error handling

class ParserSyntaxError(Exception):
    pass

class LexerReadError(Exception):
    pass

#################### Lexer

# all tokens

tokens = (
    'ID', 'NUMBER',
    'AND','OR','NOT','EQVI','IMPL',
    'PTRUE', 'PFALSE',
    'LPAREN','RPAREN',
    'LEQ', 'GEQ', 'LT', 'GT', 'EQ',
    'ASSIGN',
    'PLUS', 'MINUS', 'TIMES',
    'COLON', 'SEMICOLON', 'COMMA',
    'LBRACK', 'RBRACK',
    'LBRACE', 'RBRACE',
    'TYPE', 'TRANSITION',
    'SOURCE', 'SOURCEFORMULA',
    'EXISTS', 'FORALL', 'IF',
    'AT',
    'CTLTARGET',
    'EX', 'EG', 'EF', 'E',
    'AX', 'AG', 'AF', 'A', 'U'
    )

# Tokens are the lexical elements as recognized by the lexical analyzer
# The names of all tokens start with t_ .

t_PLUS    = r'\+'
t_MINUS   = r'-'
t_TIMES   = r'\*'
t_ASSIGN      = r':='
t_EQ      = r'='
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_LBRACK  = r'\['
t_RBRACK  = r'\]'
t_LBRACE  = r'\{'
t_RBRACE  = r'\}'
t_SEMICOLON = r';'
t_COLON = r':'
t_COMMA = r'\,'
t_LEQ = r'\<\='
t_GEQ = r'\>\='
t_LT = r'\<'
t_GT = r'\>'
t_AT = r'\@'

# Numbers

def t_NUMBER(t):
    r'\d+'
    try:
        t.value = int(t.value)
    except ValueError:
        print("Integer value too large %d", t.value)
        t.value = 0
        raise LexerReadError
    return t

# Ignored characters
t_ignore = " \t"

def t_newline(t):
    r'\n+'
    t.lexer.lineno += t.value.count("\n")
    
# Comments in the specifications start with # just like in Python

def t_COMMENT(t):
    r'\#.*'
    pass
    # No return value. Token discarded

# Process characters that are not handled by the lexer
    
def t_error(t):
    print("Illegal character '%s' on line %i" % (t.value[0],t.lineno))
    t.lexer.skip(1)
    raise LexerReadError

# IDs and reserved words

# Mapping from reserved words to tokens

keywords = {'and': 'AND',
            'or': 'OR',
            'not': 'NOT',
            'eqvi': 'EQVI',
            'impl': 'IMPL',
            'transition': 'TRANSITION',
            'type': 'TYPE',
            'source': 'SOURCE',
            'sourceformula': 'SOURCEFORMULA',
            'trajectoryformula': 'TRAJECTORYFORMULA',
            'TRUE' : 'PTRUE',
            'FALSE' : 'PFALSE',
            'forall' : 'FORALL',
            'exists' : 'EXISTS',
            'if' : 'IF',
            'ctltarget': 'CTLTARGET',
            'ctlEX' : 'EX', 'ctlAX' : 'AX',
            'ctlEG' : 'EG', 'ctlAG' : 'AG',
            'ctlEF' : 'EF', 'ctlAF' : 'AF',
            'ctlE' : 'E', 'ctlA' : 'A', 'ctlU' : 'U'
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

# Dictionary of types, indexed by names of the types

names = { }

# Set of transitions/actions, each represented as a 4-tuple
#  (name of action,       a string
#   parameters,           list of pairs (paramname,valuedomain)
#   condition,            a formula
#   effects)              list of effects (atoms, negated atoms)

actions = list()

# List of initial atoms, indicating which state variables are initially true
# or, a formula representing the set of initial states

source = None

# Target formula (initially None, to detect if no formula given)

ctltarget = None

# Named constant available for the whole specification

globalbindings = dict()

def getBindingFunc():
    return (lambda v : globalbindings[v])

####### Parser

# How strongly do the different operators bind, and whether the operator
# is left or right associative. This is important when there are no
# parentheses to disambiguate.
# For example, 1+2+3 means (1+2)+3, and 1+2*3 means 1+(2*3).
# Weaker operators are given first, stronger ones later.

precedence = (
    ('left','EX','AX','EG','AG','EF','AF'),
    ('left','PLUS','MINUS'),
    ('left','TIMES'),
    ('left','FORALL','EXISTS'),
    ('right','EQVI'),
    ('right','IMPL'),
    ('left','AND','OR'),
    ('left','NOT')
    )

# Parsing rules

# This is a context-free grammar (ply probably implement LALR grammars).
# In a rule  'nonterminal | el1 el2 el3 ... elN'
# the values associated with the syntactic elements el1,el2,...,elN
# (which are either terminals (as recognized by the lexical analyzer)
#  or terminals) can be accessed as t[1],t[2],...,t[N], and
# the value to be associated with the 'nonterminal' is assigned to t[0].

# Top-level definitions

def p_spec(t):
    '''spec : statement
            | statement spec'''
    t[0] = 0

# Named constant

def p_constant_definition(t):
    'statement : ID EQ NUMBER SEMICOLON'
    globalbindings[t[1]] = int(t[3])

# Type definition, associating some values with a type name

def p_type_definition(t):
    'statement : TYPE ID EQ setexpr SEMICOLON'
    names[t[2]] = t[4]

# One source state expressed as a list of atoms (those that are True)

def p_sourceN(t):
    'statement : SOURCE initlist SEMICOLON'
    global source
    if source != None:
        print("WARNING: Overriding earlier 'source' declaration")
    source = t[2]

# Set of source states expressed as a formula

def p_sourceFormula(t):
    'statement : SOURCEFORMULA boolexpr SEMICOLON'
    global source
    if source != None:
        print("WARNING: Overriding earlier 'source' declaration")
    source = t[2]

# CTL formula to be model-checked

def p_ctlTarget(t):
    'statement : CTLTARGET CTLformula SEMICOLON'
    global ctltarget
    ctltarget = t[2]


# Different value domains for types

# Integer range [n,m] for integers n,n+1,n+2,...,m.

def p_setexpr_interval(t):
    'setexpr : LBRACK tnumexpr COMMA tnumexpr RBRACK'
    V = getBindingFunc()
    lb = t[2].eval(V)
    ub = t[4].eval(V)
    t[0] = { x for x in range(lb,ub+1) }

# List of 'names'

def p_setexpr_enumed(t):
    'setexpr : LBRACE stringlist RBRACE'
    t[0] = t[2]

# Named type, the values for which are obtained from 'names'

def p_setexpr_named(t):
    'setexpr : ID'
    t[0] = names[t[1]]

# List of enumerated values, either integers or alphanumeric names

def p_stringlist1(t):
    'stringlist : enum'
    t[0] = { t[1] }

def p_enum(t):
    '''enum : ID
            | NUMBER'''
    t[0] = t[1]

def p_stringlistN(t):
    'stringlist : enum COMMA stringlist'
    t[0] = t[3].union({ t[1] })

# Boolean formulas

# Binary connectives

def p_boolexpr_binop(t):
    '''boolexpr : boolexpr AND boolexpr
                | boolexpr OR boolexpr
                | boolexpr IMPL boolexpr
                | boolexpr EQVI boolexpr'''
    if t[2] == 'and'   : t[0] = CONJ([t[1],t[3]])
    elif t[2] == 'or'  : t[0] = DISJ([t[1],t[3]])
    elif t[2] == 'impl': t[0] = IMPL(t[1],t[3])
    elif t[2] == 'eqvi': t[0] = EQVI(t[1],t[3])

# The only unary connective for negation

def p_boolexpr_unop(t):
    '''boolexpr : NOT boolexpr'''
    t[0] = NEG(t[2])

# Boolean constants TRUE and FALSE

def p_boolexpr_true(t):
    '''boolexpr : PTRUE'''
    t[0] = TRUE()

def p_boolexpr_false(t):
    '''boolexpr : PFALSE'''
    t[0] = FALSE()

# Exists and Forall quantification

def p_boolexpr_exists(t):
    '''boolexpr : EXISTS LPAREN paramlist RPAREN boolexpr %prec EXISTS'''
    t[0] = DISJ(allExprInstances(t[3],t[5],[]))

def p_boolexpr_forall(t):
    '''boolexpr : FORALL LPAREN paramlist RPAREN boolexpr %prec FORALL'''
    t[0] = CONJ(allExprInstances(t[3],t[5],[]))

# Comma separated list of Boolean expressions

def p_boolexprlist1(t):
    '''boolexprlist : boolexpr'''
    t[0] = [ t[1] ]

def p_boolexprlist(t):
    '''boolexprlist : boolexpr COMMA boolexprlist'''
    t[0] = [ t[1] ] + t[3]

# Atomic propositions

def p_boolexpr_atom(t):
    'boolexpr : atom'
    t[0] = AT(t[1])

# Timed atomic propositions (for trajectoryformula)

def p_boolexpr_timed_atom(t):
    'boolexpr : atom AT NUMBER'
    t[0] = TIMEDAT(t[1],t[3])

# Parentheses around Boolean formulas

def p_boolexpr_parentheses(t):
    '''boolexpr : LPAREN boolexpr RPAREN'''
    t[0] = t[2]

# Arithmetic inequalities on numeric expressions

# (We needed to put inside the square brackets because
# the LALR parser otherwise has a reduce/reduce conflict
# on numexpr : atom and boolexpr : atom.)

def p_boolexpr_numrel_GT(t):
    '''boolexpr : LBRACK numexpr GT numexpr RBRACK'''
    t[0] = NumGT(t[2],t[4])

def p_boolexpr_numrel_LT(t):
    '''boolexpr : LBRACK numexpr LT numexpr RBRACK'''
    t[0] = NumLT(t[2],t[4])

def p_boolexpr_numrel_GEQ(t):
    '''boolexpr : LBRACK numexpr GEQ numexpr RBRACK'''
    t[0] = NumGEQ(t[2],t[4])

def p_boolexpr_numrel_LEQ(t):
    '''boolexpr : LBRACK numexpr LEQ numexpr RBRACK'''
    t[0] = NumLEQ(t[2],t[4])

def p_boolexpr_numrel_EQ(t):
    '''boolexpr : LBRACK numexpr EQ numexpr RBRACK'''
    t[0] = NumEQ(t[2],t[4])

# CTL formulas

def p_ctlformula_binop(t):
    '''CTLformula : CTLformula AND CTLformula
                  | CTLformula OR CTLformula
                  | CTLformula IMPL CTLformula
                  | CTLformula EQVI CTLformula'''
    if t[2] == 'and'   : t[0] = CONJ([t[1],t[3]])
    elif t[2] == 'or'  : t[0] = DISJ([t[1],t[3]])
    elif t[2] == 'impl': t[0] = IMPL(t[1],t[3])
    elif t[2] == 'eqvi': t[0] = EQVI(t[1],t[3])

def p_ctlformula_true(t):
    'CTLformula : PTRUE'
    t[0] = TRUE()

def p_ctlformula_false(t):
    'CTLformula : PFALSE'
    t[0] = FALSE()

def p_ctlformula_not(t):
    'CTLformula : NOT CTLformula'
    t[0] = NEG(t[2])

def p_ctlformula_atom(t):
    'CTLformula : atom'
    t[0] = AT(t[1])

def p_ctlformula_parentheses(t):
    '''CTLformula : LPAREN CTLformula RPAREN'''
    t[0] = t[2]

# The three 'primitive' CTL operators E NEXT, E ALWAYS, E UNTIL

def p_ctlformula_EX(t):
    '''CTLformula : EX CTLformula'''
    t[0] = CTLopEX(t[2])

def p_ctlformula_EG(t):
    '''CTLformula : EG CTLformula'''
    t[0] = CTLopEG(t[2])

def p_ctlformula_EU(t):
    '''CTLformula : E LBRACK CTLformula U CTLformula RBRACK'''
    t[0] = CTLopEU(t[3],t[5])

# Other CTL operators are reduced to EX, EG, EU

def p_ctlformula_EF(t):
    '''CTLformula : EF CTLformula'''
    t[0] = CTLopEU(TRUE(),t[2])

def p_ctlformula_AX(t):
    '''CTLformula : AX CTLformula'''
    t[0] = NEG(CTLopEX(NEG(t[2])))

def p_ctlformula_AG(t):
    '''CTLformula : AG CTLformula'''
    t[0] = NEG(CTLopEU(TRUE(),NEG(t[2])))

def p_ctlformula_AU(t):
    '''CTLformula : A LBRACK CTLformula U CTLformula RBRACK'''
    t[0] = CONJ([NEG(CTLopEU(NEG(t[3],CONJ([NEG(t[3]),NEG(t[5])])))),NEG(CTLopEG(NEG(t[5])))])

def p_ctlformula_AF(t):
    '''CTLformula : AF CTLformula'''
    t[0] = NEG(CTLopEG(NEG(t[2])))

# Numeric expressions for Boolean formulas

def p_numexpr_parentheses(t):
    '''numexpr : LPAREN numexpr RPAREN'''
    t[0] = t[2]

def p_numexpr1(t):
    'numexpr : NUMBER'
    t[0] = NumINTCONST(t[1])

def p_numexpr3(t):
    'numexpr : atom'
    t[0] = NumINTVAR(t[1])

# Arithmetic operations

def p_numexpr(t):
    '''numexpr : numexpr PLUS numexpr
               | numexpr MINUS numexpr
               | numexpr TIMES numexpr'''
    if t[2] == '+': t[0] = NumPLUS(t[1],t[3])
    elif t[2] == '-' : t[0] = NumMINUS(t[1],t[3])
    elif t[2] == '*' : t[0] = NumTIMES(t[1],t[3])

# Numeric expressions for terms

def p_tnumexpr_parentheses(t):
    '''tnumexpr : LPAREN numexpr RPAREN'''
    t[0] = t[2]

def p_tnumexpr1(t):
    'tnumexpr : NUMBER'
    t[0] = NumINTCONST(t[1])

# Inside terms, only parameters allowed, not state variables

def p_tnumexpr2(t):
    'tnumexpr : ID'
    if t[1] in globalbindings:
        t[0] = NumINTCONST(globalbindings[t[1]])
    else:
        t[0] = NumINTVAR(t[1])

def p_tnumexpr(t):
    '''tnumexpr : tnumexpr PLUS tnumexpr
                | tnumexpr MINUS tnumexpr
                | tnumexpr TIMES tnumexpr'''
    if t[2] == '+': t[0] = NumPLUS(t[1],t[3])
    elif t[2] == '-' : t[0] = NumMINUS(t[1],t[3])
    elif t[2] == '*' : t[0] = NumTIMES(t[1],t[3])

# Terms (part of the name of a Boolean atomic proposition)

def p_termlistN(t):
    'termlist : term COMMA termlist'
    t[0] = [t[1]] + t[3]

def p_termlist1(t):
    'termlist : term'
    t[0] = [t[1]]

# Terms can be numbers, computed from an arithmetic expressions

def p_term_numeric(t):
    'term : tnumexpr'
    t[0] = t[1]

# Atoms (Boolean valued state variables P(t1,...,tn) consisting of
#        a predicate symbol P and a list of terms t1,...,tn)

def p_atom0(t):
    'atom : ID'
    t[0] = (t[1],list())

def p_atom(t):
    'atom : ID LPAREN termlist RPAREN'
    t[0] = (t[1],t[3])

# Atom lists for initial states

def p_initlist1(t):
    'initlist : atom'
    t[0] = [ t[1] ]

def p_initlistN(t):
    'initlist : atom COMMA initlist'
    t[0] = [ t[1] ] + t[3]

def p_initlistnum1(t):
    'initlist : atom EQ NUMBER'
    t[0] = [ (t[1],t[3]) ]

def p_initlistnumN(t):
    'initlist : atom EQ NUMBER COMMA initlist'
    t[0] = [ (t[1],t[3]) ] + t[5]

### Transition syntax

# effect list

def p_effect1(t):
    '''effects : effect'''
    t[0] = [ t[1] ]

def p_effects(t):
    '''effects : effect effects'''
    t[0] = [ t[1] ] + t[2]

# Boolean effects: State variable becomes True or False.
# Either an atom or a negated atom, represented as
# a pair (atom name,1) or a pair (atom name,0).

def p_effectP(t):
    '''effect : atom SEMICOLON'''
    t[0] = MAKETRUE(t[1])

def p_effectN(t):
    '''effect : NOT atom SEMICOLON'''
    t[0] = MAKEFALSE(t[2])

# Numeric effects

def p_effectA(t):
    '''effect : atom ASSIGN numexpr SEMICOLON'''
    t[0] = ASSIGN(t[1],t[3])

# Conditional effects

def p_effectC(t):
    '''effect : IF boolexpr LBRACE effects RBRACE'''
    if len(t[3]) > 1:
        t[0] = IFTHEN(t[2],EFFLIST(t[4]))
    else:
        t[0] = IFTHEN(t[2],t[4][0])

# Forall quantified effects

def p_effectU(t):
    '''effect : FORALL LPAREN paramlist RPAREN LBRACE effects RBRACE'''
    t[0] = EFFLIST([ e for eff in t[6] for e in allEffectInstances(t[3],eff,[]) ])

# transition's parameters

def p_paramlist1(t):
    '''paramlist : param'''
    t[0] = [ t[1] ]

def p_paramlistN(t):
    '''paramlist : param COMMA paramlist'''
    t[0] = [ t[1] ] + t[3]

def p_param(t):
    '''param : ID COLON setexpr'''
    t[0] = (t[1],t[3])

# transitions

def p_transition(t):
    'statement : TRANSITION ID LPAREN paramlist RPAREN boolexpr LBRACE effects RBRACE'
    if len(t[8]) > 1:
        actions.insert(0, (t[2],t[4],t[6],EFFLIST(t[8])) )
    else:
        actions.insert(0, (t[2],t[4],t[6],t[8][0]) )

def p_transition0(t):
    'statement : TRANSITION ID LPAREN RPAREN boolexpr LBRACE effects RBRACE'
    if len(t[7]) > 1:
        actions.insert(0, (t[2],[],t[5],EFFLIST(t[7])) )
    else:
        actions.insert(0, (t[2],[],t[5],t[7][0]) )

# Error rule

def p_error(t):
    print("Syntax error at '%s' on line %i" % (t.value,t.lexer.lineno))
    raise ParserSyntaxError

import ply.yacc as yacc
parser = yacc.yacc()

def parseinputfile(filename):
    global source
    global ctltarget
    with open(filename, 'r') as f:
        allinput = f.read()
        parser.parse(allinput)
    if source == None and trajectory == None:
        print("No explicit 'source' declaration given: assuming source = TRUE")
        source = TRUE()
    if ctltarget == None:
        print("Must give CTL target formula")
        raise ParserSyntaxError
    return source,ctltarget,actions
