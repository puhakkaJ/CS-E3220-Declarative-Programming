#!/usr/bin/python3

"""Solve an integer interval coloring problem with a SAT solver."""

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

from encode import encode
from solve_and_decode import solve_and_decode, ModelValidationError


def main():
    """The main method for command line use."""
    argp = argparse.ArgumentParser(
        description='Solve an integer interval coloring problem '
                    'with a SAT solver.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    argp.add_argument('n', type=int,
                      help='the size of the interval [1..n]')
    argp.add_argument('nof_colors', type=int,
                      help='the number of allowed colors')
    argp.add_argument('nof_solutions', type=int, default=0, nargs='?',
                      help='find at most this many solutions (0 means all)')
    argp.add_argument('--dont_print_solutions', action='store_true',
                      help='do not print the found solutions')
    argp.add_argument('--break_symmetries', action='store_true',
                      help='find only non-isomorphic solutions')
    args = argp.parse_args()

    if not args.n >= 1:
        argp.error('n must be positive')
    if not args.nof_colors >= 1:
        argp.error('the amount of colors must be positive')

    cnf = encode(args.n, args.nof_colors, args.break_symmetries)
    # Uncomment to print the formula
    # print(cnf.to_fp(sys.stdout))

    try:
        solve_and_decode(args.n, args.nof_colors, args.break_symmetries,
                         cnf,
                         args.nof_solutions, not args.dont_print_solutions)
    except ModelValidationError as err:
        sys.stderr.write(str(err)+'\n')
        sys.exit(1)


if __name__ == "__main__":
    main()
