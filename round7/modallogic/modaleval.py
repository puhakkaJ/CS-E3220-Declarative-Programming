#!/usr/bin/python3

import sys

from modalparser import parseinputfile, ParserSyntaxError, LexerReadError
from modallogic import *

def main():
    if len(sys.argv) != 2:
        print("Must give exactly one argument [file]")
        exit(1)
    args = sys.argv
    filename = args[1]

    print("Input file: " + filename)

    try:
        KM,formulas = parseinputfile(filename)
    except ParserSyntaxError:
        print("Parser error: exiting...")
        exit(1)
    except LexerReadError:
        print("Lexer error: exiting...")
        exit(1)

    # Show model

    print("KRIPKE MODEL:")

    for w in KM.worlds:
        print(w + " { " + ','.join(KM.valuation[w]) + " } " + ','.join(KM.neighbors(w)))

    w0 = KM.worlds[0]

    # Evaluate all formulas

    print("VALUES OF FORMULAS IN " + w0 + ":")

    for f in formulas:
        print("Formula " + str(f) + " is " + ('TRUE' if f.eval(KM,w0) else 'FALSE'))

main()
