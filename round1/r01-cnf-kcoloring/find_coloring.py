#!/usr/bin/python3

"""Solve a graph k-coloring problem with a SAT solver."""

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

from read_graph import read_graph
from encode import encode
from solve_and_decode import solve_and_decode, ModelValidationError


def main():
    """The main method for command line use."""
    argp = argparse.ArgumentParser(
        description='Solve a graph k-coloring problem with a SAT solver.',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    argp.add_argument('graph', type=str,
                      help='the name of the graph file')
    argp.add_argument('k', type=int,
                      help='the number of available colors')
    argp.add_argument('--all_solutions', action='store_true',
                      help='enumerate all solutions')
    argp.add_argument('--dont_print_solutions', action='store_true',
                      help='do not print the found solutions')
    args = argp.parse_args()

    if args.k <= 0:
        argp.error("the number of colors must be positive")

    (nof_vertices, edges) = read_graph(args.graph)
    # Uncomment these to see the graph
    # print(nof_vertices)
    # print(edges)

    cnf = encode(nof_vertices, edges, args.k)
    # Uncomment to print the formula
    # print(cnf.to_fp(sys.stdout))

    try:
        solve_and_decode(nof_vertices, edges, args.k, cnf,
                         args.all_solutions, not args.dont_print_solutions)
    except ModelValidationError as err:
        sys.stderr.write(str(err)+'\n')
        sys.exit(1)


if __name__ == "__main__":
    main()
