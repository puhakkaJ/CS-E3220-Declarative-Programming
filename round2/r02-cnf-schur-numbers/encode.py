#
# Author: Tommi Junttila, Aalto University.
# Only personal student use on the Aalto University course
# CS-E3220 Declarative Programming is allowed.
# Redistribution in any form, including posting to public or
# shared repositories or forums, is not allowed.
#

"""Encode an integer interval coloring problem instance to a CNF instance."""

# Do not change or add import statements
from pysat.formula import CNF


def encode(n: int, nof_colors: int, break_symmetries: bool) -> CNF:
    """Encode an integer interval coloring problem instance
    to a CNF instance."""

    assert n >= 1, 'n must be positive'
    assert nof_colors >= 1, "the amount of colors must be positive"

    # A helper function that you *should* use!
    # Do NOT modify
    def v_cnf(i: int, c: int) -> int:
        """Return the positive integer CNF variable number
        for the encoding variable v_{i,c} denoting
        that the number i should be colored with the color c."""
        assert 1 <= i <= n
        assert 1 <= c <= nof_colors
        return (i-1)*nof_colors+(c-1)+1

    # The number of variables in the instance; at least n*nof_colors
    # Do NOT modify
    nof_vars = n*nof_colors

    # A helper function that you may use (you do NOT have to).
    # If you use auxiliary variables, make sure that they do not introduce
    # extra solutions, i.e. solutions that are the same when projected to
    # the important variables of form v_{i,c}.
    # Do NOT modify
    def new_aux_variable() -> int:
        """Allocate a new auxiliary CNF variable."""
        nonlocal nof_vars
        nof_vars += 1
        return nof_vars

    # The clauses in the CNF instance.
    # To add a clause such as (v_{1,1} | !v_{1,2} | !v_{1,3}),
    # write clauses.append([v_cnf(1,1),-v_cnf(1,2),-v_cnf(1,3)]).
    # Do NOT modify
    cnf = CNF()

    # INSERT YOUR CODE HERE
    # It should only add appropriate clauses to "cnf"

    # Every i has a color
    for i in range(1, n + 1):
        cnf.append([v_cnf(i, c) for c in range(1, nof_colors + 1)])
    
    # Every i has one and only one color
    for i in range(1, n + 1):
        for c1 in range(1, nof_colors + 1):
            for c2 in range(c1 + 1, nof_colors + 1):
                cnf.append([-v_cnf(i, c1), -v_cnf(i, c2)])

    # i1 and i2 and i1 + i2 can not have a same color if i1 + i2 <= n
    for c in range(1, nof_colors + 1):
        for i1 in range(1, n + 1):
            for i2 in range(1, n + 1):
                if i1 + i2 <= n:
                    cnf.append([-v_cnf(i1, c), -v_cnf(i2, c), -v_cnf(i1 + i2, c)])

    # Symmetry breaking if requested
    if break_symmetries:
        # If/when you implement the symmetry reduction,
        # replace "pass" with your own code
        # OPTIONALLY INSERT YOUR CODE HERE

        # 1 + 1 = 2
        cnf.append([v_cnf(1, 1)])

        # 2 + 2 = 4
        if n >= 2 and nof_colors >= 2:
            cnf.append([v_cnf(2, 2)])

        # See symmetry breaking in https://arxiv.org/abs/1711.08076
        if nof_colors >= 4 and n >= 3:
            for i1 in range (3, n + 1):
                # construct the last boundary clause
                clauses = []

                for i2 in range(3, i1):
                    clauses.append(v_cnf(i2, nof_colors - 1))
                
                clauses.append(-v_cnf(i1, nof_colors))
                # Add to the cnf list
                cnf.append(clauses)

    return cnf
