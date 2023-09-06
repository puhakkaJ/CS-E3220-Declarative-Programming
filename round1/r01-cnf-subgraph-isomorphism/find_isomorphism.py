#!/usr/bin/python3

"""Solve an induced sub-graph isomorphism problem with a SAT solver."""

#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

# Do NOT edit or add the import statements
import argparse
import sys

from graph import Graph
from encode import encode
from solve_and_decode import solve_and_decode, ModelValidationError


def main():
    """The main method for command line use."""
    argp = argparse.ArgumentParser(
        description='Solve an induced sub-graph isomorphism problem '
                    'with a SAT solver.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    argp.add_argument('pattern', type=str,
                      help='the name of the pattern graph file')
    argp.add_argument('target', type=str,
                      help='the name of the target graph file')
    argp.add_argument('nof_solutions', type=int, default=0, nargs='?',
                      help='find at most this many solutions (0 means all)')
    argp.add_argument('--dont_print_solutions', action='store_true',
                      help='do not print the found solutions')
    args = argp.parse_args()

    # Read the pattern and target graphs
    pattern = Graph.read(args.pattern)
    target = Graph.read(args.target)

    cnf = encode(pattern, target)
    # Uncomment to print the formula
    # print(cnf.to_fp(sys.stdout))

    try:
        solve_and_decode(pattern, target, cnf,
                         args.nof_solutions, not args.dont_print_solutions)
    except ModelValidationError as err:
        sys.stderr.write(str(err)+'\n')
        sys.exit(1)


if __name__ == "__main__":
    main()
